-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialC_prop_2_28_exists_boundary_arc
-- name    : DiscreteConvex.CombinatorialC.prop_2_28_exists_boundary_arc
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:44:48.459343+00:00
-- url     : https://prove2.me/theorems/d35783a6-2042-4e86-b7cb-0051cac51d5b
-- title:
--   Proposition 2.28 -- existence of a sign-changing arc in the series set
-- statement:
--   Under the optimality-derived hypotheses, there exists $b\in(\operatorname{supp}^+(\pi_1)\cap S)\cap\operatorname{supp}^-(w_1-w_2)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.88, Proposition 2.28.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.88, Proposition 2.28

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsCircuit
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppPosR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.88, Proposition 2.28, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Proposition 2.28.** There exists `b ∈ (supp⁺(π1) ∩ S) ∩ supp⁻(w1 - w2)`. The surrounding
hypotheses (`π1` a circuit, `a ∈ supp⁺(π1) ∩ S`, `⟨w1,π1⟩ ≤ 0`, `⟨w2,-π1⟩ ≤ 0`, from the
optimality of `ξ1` for `w1` and `ξ2` for `w2` established in the proof text just above) are
carried explicitly as hypotheses, since the boxed proposition itself is stated in that local
context rather than as a free-standing claim. -/
theorem prop_2_28_exists_boundary_arc {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V]
    [DecidableEq A] (src dst : A → V) (S : Finset A) (w1 w2 : A → ℝ) (pi1 : A → ℝ) (a : A)
    (hpi1 : IsCircuit src dst pi1) (ha : a ∈ SuppPosR pi1 ∩ S)
    (hw1 : dotProduct w1 pi1 ≤ 0) (hw2 : dotProduct w2 (-pi1) ≤ 0)
    (haw : 0 < w1 a - w2 a) :
    ∃ b ∈ SuppPosR pi1 ∩ S, w1 b - w2 b < 0 := by sorry

end DiscreteConvex.CombinatorialC
