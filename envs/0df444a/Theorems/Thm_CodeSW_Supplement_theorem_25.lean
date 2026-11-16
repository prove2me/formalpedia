-- Prove2me | Theorems.Thm_CodeSW_Supplement_theorem_25
-- name    : CodeSW.Supplement.theorem_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:51:05.608926+00:00
-- url     : https://prove2.me/theorems/9a9b90cc-4ad3-423e-926b-25ae557cdbf2
-- title:
--   Theorem 25 — the Code SW chain for the 3-spin Curie-Weiss model at $\beta^*=c^*/n^2$ mixes in time $\exp(\Omega(n))$
-- statement:
--   For $n\ge3$ let $h_n\in\{0,1\}^{\binom n3\times n}$ be the parity check matrix of the ferromagnetic 3-spin Curie-Weiss model, whose rows are all strings of Hamming weight $3$, so that $H(x)=2|h_nx|=2\binom{|x|}{3}+2|x|\binom{n-|x|}{2}$ (eq. (11)). Let $c^*$ be the critical constant of Lemma 23 ($4.0324<c^*<4.0326$), $\beta^*_n=c^*/n^2$, $P_n$ the Code Swendsen-Wang chain (Algorithm 2) of $h_n$ at $\beta^*_n$, and $\pi_n$ the Gibbs distribution of $h_n$ at $\beta^*_n$. Write
--   $$d_n(t)=\max_{x}\big\|P_n^t(x,\cdot)-\pi_n\big\|_{\mathrm{TV}}.$$
--   Then there are constants $a>0$ and $N$ such that for every $n\ge N$,
--   $$d_n(t)>\frac1{2e}\qquad\text{for every integer }t<e^{an},$$
--   that is, the mixing time $\tau(P_n)=\min\{t:\max_x\sum_y|P_n^t(x,y)-\pi_n(y)|\le e^{-1}\}$ is at least $e^{an}$.
--
--   The theorem shows that the Code Swendsen-Wang dynamics, which mixes rapidly for graphic and cographic codes, is torpid at the first-order phase transition of the 3-spin Curie-Weiss model, where an ordered and a disordered phase coexist.
--
--   **Formalization Note** The rows of $h_n$ are indexed by an enumeration of the 3-element subsets of $[n]$, and the statement holds for every enumeration. $a$ and $N$ are fixed before $n$.
--
--   Differences from the source:
--   - reading: the mixing time … is exp(Ω(n)) → ∃ a > 0, ∃ N, ∀ n ≥ N, d(t) > 1/(2e) for every t < e^{an}; reason: Ω(n) has an n-independent constant; τ is a minimum, so τ ≥ T exactly when the chain is not yet mixed at every t < T
--   - encoding: τ(P) = min_t [max_x ∑_y |P^t(x,y) − π(y)| ≤ e^{−1}] (p.13) → MarkovMixing.distStationary (max_x total variation) compared with 1/(2e); reason: total variation is half the ℓ¹ distance; same quantity
--   - encoding: h_n with rows all strings of Hamming weight 3 → threeSpinCheck n e for every enumeration e of the 3-subsets by Fin (n.choose 3); reason: the Code SW chain and π do not depend on the order of the checks, so every enumeration gives the same instance
--   - encoding: c* of Lemma 23, with u* the unique zero of J in (0,1) → cStar = ln((1+u*)/(1−u*))/u*² with u* = sup{u ∈ (0,1) : J(u) > 0}; reason: J > 0 on (0,u*) and J < 0 on (u*,1), so the supremum is the zero; the formula is the one in Lemma 23's proof
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Theorem 25, p.27; model eq. (11), p.25; c* in Lemma 23's proof, p.26; mixing time τ, p.13; informal version Theorem 3, p.5

import Definitions.Def_CodeSW_Supplement_threeSpinCheck
import Definitions.Def_CodeSW_cswKernel
import Definitions.Def_mm_mixing

set_option autoImplicit false

open Matrix

namespace CodeSW.Supplement

/-- **Theorem 25 (torpid mixing for the 3-spin Curie-Weiss model).** The mixing time of the Code SW
dynamics for the ferromagnetic 3-spin Curie-Weiss model (11) at inverse temperature `β* = c*/n²`
is `exp(Ω(n))`: there are `a > 0` and `N` such that for every `n ≥ N` (and every enumeration of the
checks of `h_n`) the Code SW chain is still at total variation distance more than `1/(2e)` from the
Gibbs distribution, from some starting state, at every time `t < e^{an}`
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, Theorem 25, p.27; informal version Theorem 3, p.5).

**Formalization Note** The mixing time `τ(P) = min_t [max_x ∑_y |P^t(x,y) − π(y)| ≤ e^{−1}]` of
p.13 is an `ℓ¹` threshold, i.e. total variation `1/(2e)`; "`τ ≥ e^{an}`" is "`d(t) > 1/(2e)` for
every `t < e^{an}`". `a` and `N` are fixed before `n`. `c*` is the explicit constant `cStar` of
Lemma 23's proof (p.26). The chain is `cswKernel` (Algorithm 2, `p = 1 − e^{−2β*}`). -/
theorem theorem_25 :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ e : Fin (n.choose 3) ≃ {s : Finset (Fin n) // s.card = 3},
        ∀ t : ℕ, (t : ℝ) < Real.exp (a * n) →
          1 / (2 * Real.exp 1) <
            MarkovMixing.distStationary (CodeSW.cswKernel (threeSpinCheck n e) (cStar / (n : ℝ) ^ 2))
              (CodeSW.gibbs (threeSpinCheck n e) (cStar / (n : ℝ) ^ 2)) t := by sorry

end CodeSW.Supplement
