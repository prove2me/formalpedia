-- Prove2me | Theorems.Thm_DiazModulus_generic_conj_pair_no_quadratic_relation
-- name    : DiazModulus.generic_conj_pair_no_quadratic_relation
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T20:37:21.505686+00:00
-- url     : https://prove2.me/theorems/d6ad726a-a8a5-4bd5-ba3b-ab7d391b7449
-- title:
--   A point u of a circle of algebraic radius, algebraically independent of π, satisfies no rational quadratic relation with ū and iπ
-- statement:
--   **No homogeneous quadratic relation among $u, \bar u, i\pi$.**
--
--   Let $u \neq 0$ with $|u|^{2}$ algebraic, and suppose $u$ and $i\pi$ are algebraically independent over $\overline{\mathbb{Q}}$. If a rational quadratic form $F(X_1, X_2, X_3) = \sum_{k,l} F_{kl} X_k X_l$ vanishes at $(u, \bar u, i\pi)$, then $F$ is the zero form:
--
--   $$F_{kl} + F_{lk} = 0 \quad\text{for all } k, l.$$
--
--   The only algebraic relation of $(u, \bar u)$ is the inhomogeneous $u\bar u = |u|^{2}$, and adjoining the period $i\pi$ adds none. For a candidate of Diaz's conjecture that is algebraically independent of $\pi$, these are exactly the logarithms the candidate certifies: $u$, $\bar u$ and $i\pi$. The consequence is `DiazModulus.generic_conj_pair_four_exp_barrier`. The statement does not use $e^{u}$ and holds for every point of the circle that is generic in this sense.
--
--   **Novelty.** Elementary. Novelty is not asserted.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Theorem 5.4(a). Novelty is not asserted. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem generic_conj_pair_no_quadratic_relation (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (F : Fin 3 → Fin 3 → ℚ)
    (h : ∑ k, ∑ l, (F k l : ℂ) * (![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k * ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] l) = 0) :
    ∀ k l, F k l + F l k = 0 := by sorry

end DiazModulus
