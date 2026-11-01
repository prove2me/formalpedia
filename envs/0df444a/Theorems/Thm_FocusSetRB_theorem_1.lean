-- Prove2me | Theorems.Thm_FocusSetRB_theorem_1
-- name    : FocusSetRB.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:48.641955+00:00
-- url     : https://prove2.me/theorems/1a05afc5-da3a-4687-9179-004a93c1c5dd
-- title:
--   Theorem 1, p.10 — the set-expansion policy has optimality gap at most $256\,r_{\max}\lambda_W^2|\mathbb S|^2/(\beta^2\sqrt N)$
-- statement:
--   Consider an $N$-armed restless bandit problem with single-armed MDP $(\mathbb S,\mathbb A,P,r)$ and budget $\alpha N$ for $0<\alpha<1$. Let $y^*$ be an optimal solution of (LP) whose single-armed policy $\bar\pi^*$ induces an aperiodic unichain (Assumption 1), let $\lambda_W$ be the maximal eigenvalue of the matrix $W$ of Definition 2, and let $\beta=\min\{\alpha,1-\alpha\}$. Let $\pi$ be the set-expansion policy (Algorithm 2): a focus-set policy started from $D_{-1}=\emptyset$ whose update obeys Algorithm 2, lines 2–5, and whose rectifier obeys Algorithm 1's (4)–(5). Then for every $N\ge1$ with $\alpha N$ an integer and every initial state vector $S_0$,
--
--   $$
--   R^*(N,S_0)-R^-(\pi,S_0)\le\frac{C_{\mathrm{SE}}}{\sqrt N},\qquad C_{\mathrm{SE}}=\frac{256\,r_{\max}\,\lambda_W^2\,|\mathbb S|^2}{\beta^2}.
--   $$
--
--   Here $R^*(N,S_0)$ is the optimal reward over all history-dependent randomized policies and $R^-(\pi,S_0)$ the liminf average reward of $\pi$. The set-expansion policy is therefore asymptotically optimal with an $O(1/\sqrt N)$ gap under the aperiodic-unichain assumption alone, without the global attractor or synchronization assumptions of earlier work.
--
--   Differences from the source:
--   - reading: R(π, S₀), the long-run average reward → R⁻(π, S₀), the liminf average reward; reason: p.5 defines the optimality gap as R*(N,S₀) − R⁻(π,S₀) and writes R(π,S₀) for it when the limit exists; R⁻ is always defined and equals R where the limit exists
--   - reading: C_SE "a constant depending on r_max, |𝕊|, β and P_π̄*; the explicit expression of C_SE is given in the proof" → C_SE = 256 r_max λ_W² |𝕊|² / β²; reason: the expression of the proof's closing display (p.18); λ_W depends only on P_π̄* and μ*
--   - encoding: R*(N,S₀) the optimal value of (RB) over policies that may be randomized and use the whole history → supremum of R⁻ over history-dependent randomized policies whose every action vector pulls exactly k = αN arms; reason: the class the paper describes on p.5; the budget (1a) holds at every step
--   - generalization: the set-expansion policy of Algorithm 2 ("any set with the largest m(D_t)", uniform tie-breaking in lines 6–15) → every update kernel whose possible outputs obey lines 2–5 and every rectifier kernel whose possible outputs obey Algorithm 1's (4)–(5); reason: contains Algorithm 2 with every choice of maximizer and its uniform tie-breaking; p.10 says the analysis holds whenever lines 4–5 of Algorithm 1 are satisfied
--   - encoding: μ* is the stationary distribution of P_π̄* → μ*(s) := y*(s,0) + y*(s,1); reason: the paper states this identity on p.7; it is stationary by (2b) and (3) and is the unique stationary law under Assumption 1, so the same vector
--   - encoding: λ_W the maximal eigenvalue of W → λ_W the maximal Rayleigh quotient sup over ‖u‖₂ = 1 of u W uᵀ; reason: equal for the symmetric matrix W
--   - encoding: αN an integer, N arms → k : ℕ with (k : ℝ) = α·N and N ≥ 1; reason: the paper assumes αN is an integer (p.5); an N-armed problem has N ≥ 1
--   - encoding: P_π̄* induces an aperiodic unichain (a single recurrent class and a possibly empty set of transient states) → some state is recurrent, any two recurrent states reach each other, and every recurrent state has period 1; transient states are unconstrained; reason: the same property of a finite chain spelled out state by state; the period of a state is the gcd of its return times
--   - encoding: W = ∑_{k≥0} (P_π̄* − Ξ)^k (P_π̄*ᵀ − Ξᵀ)^k → a tsum in Matrix S S ℝ with the entrywise topology; reason: the series converges under Assumption 1 (Lemma 11), so the tsum is its sum
--   - reading: D_t chosen based on X_t and D_{t−1}, actions based on X_t and D_t (Algorithm 1), "any set" in Algorithm 2 → the update and the rectifier are fixed kernels that do not depend on t; reason: Algorithm 1 names those as the inputs of the rule, and Appendix D (p.40) treats (S_t, A_t, X_t, D_t) as a finite-state Markov chain
--   - encoding: arms indexed by [N] = {1,…,N} → arms indexed by Fin N = {0,…,N−1}; reason: relabelling only
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Theorem 1, eq. (7), p.10; constant from the proof of Theorem 1, p.18

import Mathlib
import Definitions.Def_FocusSetRB_LPFeasible
import Definitions.Def_FocusSetRB_IsAperiodicUnichain
import Definitions.Def_FocusSetRB_IsSetExpansionSelector

namespace FocusSetRB

/-- **Theorem 1 (Optimality gap of set-expansion policy), eq. (7), p.10**, with the explicit
constant of its proof, p.18 (Hong, Xie, Chen, Wang, arXiv:2402.05689v4). Consider an `N`-armed restless bandit problem with the
single-armed MDP `(𝕊, 𝔸, P, r)` and budget `αN` for `0 < α < 1`. Assume that the optimal
single-armed policy induces an aperiodic unichain (Assumption 1). Let `π` be the set-expansion
policy (Algorithm 2). Then for all `N` and initial state vector `S₀`,
`R*(N, S₀) − R(π, S₀) ≤ C_SE/√N` with `C_SE = 256 r_max λ_W² |𝕊|² / β²`, `β = min{α, 1 − α}`.

Here `y` is an optimal solution of (LP) whose policy `π̄*` (3) induces an aperiodic unichain
(Assumption 1, p.7, the paper's standing assumption).

**Formalization Note.** `R(π, S₀)` is the liminf average reward `R⁻(π, S₀)` (the source's
optimality gap `R*(N, S₀) − R⁻(π, S₀)`, p.5); `R*(N, S₀)` is the supremum of `R⁻` over all
history-dependent randomized policies obeying the budget (1a) at every step. The set-expansion
policy is any focus-set process with initial focus set `D_{−1} = ∅` whose update kernel obeys
Algorithm 2's lines 2–5 (`IsSetExpansionSelector`) and whose rectifier obeys Algorithm 1's
(4)–(5) (`IsRectifier`); Algorithm 2's uniform tie-breaking (lines 6–15) is one such rectifier
(p.10). "For all `N`" is every `N ≥ 1` with `αN = k ∈ ℕ`. `λ_W` is the maximal eigenvalue of `W`
(Definition 2). -/
theorem theorem_1 {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : SingleArmMDP S) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {y : S → Bool → ℝ} (hy : IsLPOptimal M α y) (hU : IsAperiodicUnichain (Ppi M y))
    {N k : ℕ} (hN : 1 ≤ N) (hk : (k : ℝ) = α * N)
    (sel : (Fin N → S) → Finset (Fin N) → Finset (Fin N) → ℝ)
    (hsel : IsSetExpansionSelector α y sel)
    (rect : (Fin N → S) → Finset (Fin N) → (Fin N → Bool) → (Fin N → Bool) → ℝ)
    (hrect : IsRectifier k rect)
    (S0 : Fin N → S) :
    Rstar M N k S0 - focusRminus M y sel rect S0 ∅ ≤
      256 * rmax M * lamW M y ^ 2 * (Fintype.card S : ℝ) ^ 2 / (beta α ^ 2 * Real.sqrt N) := by sorry

end FocusSetRB
