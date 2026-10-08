-- Prove2me | Theorems.Thm_AMPUniversality_Universal_lemma_2
-- name    : AMPUniversality.Universal.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:44.813001+00:00
-- url     : https://prove2.me/theorems/8a20c203-f726-4c9f-9400-dbbc3f752498
-- title:
--   Lemma 2 (uniform moment bounds), pp. 22–23 — |E[zᵗᵢ(r)^m]| ≤ K and |E[zᵗᵢ→ⱼ(r)^m]| ≤ K
-- statement:
--   Let $\{(A(N), \mathcal F_N, x^{0,N})\}_{N\ge1}$ be a $(C,d)$-regular polynomial sequence of AMP instances, and let $z^t_{i\to j}$ and $z^t_i$ be the messages and vectors of the message-passing iteration (4.5)–(4.6) run with the matrix $A(N)$.
--
--   Then for every $t\ge1$, every coordinate $r \in [q]$ and every integer $m \ge 0$ there is a constant $K$, independent of $N$ (and, per Note 2, a function of $C, d, q, t, r, m$ only), such that for all $N$, all $i \in [N]$ and all $j \in [N]$ with $j\ne i$, the moments below are finite and
--
--   $$
--   \big|\mathbb E[z^t_i(r)^m]\big| \;\le\; K, \qquad \big|\mathbb E[z^t_{i\to j}(r)^m]\big| \;\le\; K .
--   $$
--
--   These uniform bounds on the moments of the message-passing iteration are reused in the proofs of the state-evolution results (Section 4.7 of the paper), where every moment of the iterates has to be bounded uniformly in $N$.
--
--   **Formalization Note** This item formalizes the second and third claims of Lemma 2, with the constant chosen before the sequence as a function of $C, d, q, t, r, m$ only (Note 2, p. 16). Its first claim, $|\mathbb E[z^t_i(r)^m] - T(A)| \le KN^{-1/2}$ (printed with "$=$"), involves the tree sum $T(A)$ from the proof of Proposition 1 and is not stated. Integrability of the moments is part of the conclusion, so the bounds cannot hold through the junk value $0$ of a non-integrable Bochner integral.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, pp. 22–23, Lemma 2 (second and third claims)

import Mathlib
import Definitions.Def_AMPUniversality_Universal_Poly
import Definitions.Def_AMPUniversality_Universal_Orbit
import Definitions.Def_AMPUniversality_Universal_Regular

namespace AMPUniversality.Universal

open MeasureTheory ProbabilityTheory

/-- Lemma 2 (pp. 22–23), second and third bounds, with Note 2: for a `(C, d)`-regular
polynomial sequence, every `t ≥ 1`, coordinate `r` and exponent `m`, the moments
`E[z^t_i(r)^m]` and `E[z^t_{i→j}(r)^m]` (`i ≠ j`) of the message-passing iteration (4.5)–(4.6)
are bounded by a constant `K` depending only on `C, d, q, t, m` (Note 2), not on `N`, `i`, `j`
or the sequence. -/
theorem lemma_2 (C : ℝ) (d q t : ℕ) (ht : 1 ≤ t) (r : Fin q) (m : ℕ) :
    ∃ K : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (A : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ)
      (c : (N : ℕ) → Ω → Fin N → ℕ → Fin q → (Fin q → Fin (d + 1)) → ℝ)
      (x0 : (N : ℕ) → Ω → Fin N → Fin q → ℝ),
      IsRegular P C d q A c x0 →
      ∀ (N : ℕ) (i j : Fin N),
        (Integrable (fun ω => mpOrbit (A N ω) (c N ω) (x0 N ω) t i r ^ m) P ∧
          |∫ ω, mpOrbit (A N ω) (c N ω) (x0 N ω) t i r ^ m ∂P| ≤ K) ∧
        (i ≠ j →
          Integrable (fun ω => mpMessages (A N ω) (c N ω) (x0 N ω) t i j r ^ m) P ∧
          |∫ ω, mpMessages (A N ω) (c N ω) (x0 N ω) t i j r ^ m ∂P| ≤ K) := by sorry

end AMPUniversality.Universal
