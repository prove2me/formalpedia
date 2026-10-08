-- Prove2me | Theorems.Thm_CorreaThreshold_Nonadaptive_eq_4
-- name    : CorreaThreshold.Nonadaptive.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:41.364843+00:00
-- url     : https://prove2.me/theorems/203f3cbd-a501-48cf-9010-bc2490447e78
-- title:
--   Equation (4), p. 1457 — multilinear relaxation of (P)
-- statement:
--   Let $q_i\in[0,1]$ be independent Bernoulli success probabilities and let $b_i\in\mathbb R$ be prizes. Equation (4) rewrites the relaxation of problem (P) as
--
--   $$F(\pi)=\sum_i b_i\pi_i\sum_{S\subseteq N\setminus\{i\}}\frac{\prod_{j\in S}\pi_j\prod_{j\in N\setminus(S\cup\{i\})}(1-\pi_j)}{1+|S|}.$$
--
--   The rewritten expression equals the original multilinear objective for every $\pi$. On the box $0\le\pi_i\le q_i$, it never exceeds the optimum of (P), and some $\pi$ in that box attains that optimum. This equivalence permits the proof to choose a convenient feasible $\pi$.
--
--   **Formalization Note** $N$ is a nonempty finite index set, represented by `Fin n` with $n\ge1$. The optimum over subsets is a finite maximum. Prizes may be negative, as the statement of Lemma 1 permits.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1457, (P) and (4); https://doi.org/10.1287/moor.2020.1105

import Mathlib
import Definitions.Def_CorreaThreshold_Nonadaptive_Bernoulli

namespace CorreaThreshold.Nonadaptive

/-- Equation (4) and the equivalence of its optimization problem with (P). -/
theorem eq_4 {n : ℕ} [NeZero n] (q b : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    (∀ π : Fin n → ℝ, relaxObj b π = objFour b π) ∧
    (∀ π : Fin n → ℝ, (∀ i, 0 ≤ π i ∧ π i ≤ q i) →
      objFour b π ≤ objP q b) ∧
    (∃ π : Fin n → ℝ, (∀ i, 0 ≤ π i ∧ π i ≤ q i) ∧
      objFour b π = objP q b) := by sorry

end CorreaThreshold.Nonadaptive
