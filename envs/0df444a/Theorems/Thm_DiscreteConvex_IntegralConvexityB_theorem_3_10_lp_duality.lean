-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexityB_theorem_3_10_lp_duality
-- name    : DiscreteConvex.IntegralConvexityB.theorem_3_10_lp_duality
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:02:30.237468+00:00
-- url     : https://prove2.me/theorems/5921cfc4-3a53-428b-be77-5996469607b0
-- title:
--   Theorem 3.10 -- LP duality
-- statement:
--   Weak duality, strong duality with attainment, and complementarity for a primal/dual LP pair.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.107, Theorem 3.10.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.107, Theorem 3.10

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_PrimalFeas
import Definitions.Def_DiscreteConvex_IntegralConvexityB_DualFeas

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.107, Theorem 3.10, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- **Theorem 3.10** (LP duality). (1) Weak duality: `c⊤x ≥ b⊤y` for `x ∈ P`, `y ∈ D`.
(2) Strong duality: if `P ≠ ∅` or `D ≠ ∅`, `inf{c⊤x | x∈P} = sup{b⊤y | y∈D}`; this common value
is finite iff both `P, D` are nonempty, in which case both extrema are attained.
(3) Complementarity: for `x ∈ P`, `y ∈ D`, both are optimal iff `x(j) = 0` or
`(A⊤y-c)(j) = 0` for every `j`. -/
theorem theorem_3_10_lp_duality {V W : Type*} [Fintype V] [Fintype W] (A : Matrix W V ℝ)
    (b : W → ℝ) (c : V → ℝ) :
    (∀ x ∈ PrimalFeas A b, ∀ y ∈ DualFeas A c, dotProduct c x ≥ dotProduct b y) ∧
      ((PrimalFeas A b).Nonempty ∨ (DualFeas A c).Nonempty →
        sInf {v : EReal | ∃ x ∈ PrimalFeas A b, v = (dotProduct c x : ℝ)} =
            sSup {v : EReal | ∃ y ∈ DualFeas A c, v = (dotProduct b y : ℝ)} ∧
          (∀ vstar : ℝ,
            sInf {v : EReal | ∃ x ∈ PrimalFeas A b, v = (dotProduct c x : ℝ)} = (vstar : EReal) ↔
              (PrimalFeas A b).Nonempty ∧ (DualFeas A c).Nonempty) ∧
          ((PrimalFeas A b).Nonempty → (DualFeas A c).Nonempty →
            (∃ x ∈ PrimalFeas A b, ∀ x' ∈ PrimalFeas A b, dotProduct c x ≤ dotProduct c x') ∧
              (∃ y ∈ DualFeas A c, ∀ y' ∈ DualFeas A c, dotProduct b y ≥ dotProduct b y'))) ∧
      (∀ x ∈ PrimalFeas A b, ∀ y ∈ DualFeas A c,
        ((∀ x' ∈ PrimalFeas A b, dotProduct c x ≤ dotProduct c x') ∧
            ∀ y' ∈ DualFeas A c, dotProduct b y ≥ dotProduct b y') ↔
          ∀ j, x j = 0 ∨ Matrix.vecMul y A j - c j = 0) := by sorry

end DiscreteConvex.IntegralConvexityB
