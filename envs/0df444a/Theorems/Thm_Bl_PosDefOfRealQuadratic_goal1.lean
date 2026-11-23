-- Prove2me | Theorems.Thm_Bl_PosDefOfRealQuadratic_goal1
-- name    : Bl.PosDefOfRealQuadratic.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:19.249949+00:00
-- url     : https://prove2.me/theorems/d2db32f3-0641-4964-b743-082135234a34
-- title:
--   Pos Def Of Real Quadratic: goal1
-- statement:
--   The Pos Def Of Real Quadratic construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/PosDefOfRealQuadratic/QuadFormRealSmul.lean#L25-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/PosDefOfRealQuadratic/QuadFormRealSmul.lean#L25-L81

import Mathlib
import Definitions.Def_Lemmata_PosDefOfRealQuadratic_QuadFormRealSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.PosDefOfRealQuadratic

theorem Bl.PosDefOfRealQuadratic.goal1 :
  ∀ {X : Type u_1} [inst : TopologicalSpace.{u_1} X] {m : Nat} (A : X → Matrix.{0, 0, 0} (Fin m) (Fin m) Complex),
  (∀ (i j : Fin m),
      @Continuous.{u_1, 0} X Complex inst
        (@UniformSpace.toTopologicalSpace.{0} Complex
          (@PseudoMetricSpace.toUniformSpace.{0} Complex
            (@SeminormedRing.toPseudoMetricSpace.{0} Complex
              (@SeminormedCommRing.toSeminormedRing.{0} Complex
                (@NormedCommRing.toSeminormedCommRing.{0} Complex
                  (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))
        fun (x : X) ↦ A x i j) →
    (∀ (x : X),
        @Matrix.IsHermitian.{0, 0} Complex (Fin m)
          (@InvolutiveStar.toStar.{0} Complex
            (@StarAddMonoid.toInvolutiveStar.{0} Complex
              (@AddCommMonoid.toAddMonoid.{0} Complex
                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
              (@StarRing.toStarAddMonoid.{0} Complex
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                Complex.instStarRing)))
          (A x)) →
      ∀ (x0 : X),
        @Matrix.PosDef.{0, 0} (Fin m) Complex Complex.instRing Complex.partialOrder Complex.instStarRing (A x0) →
          @Filter.Eventually.{u_1} X
            (fun (x : X) ↦
              @Matrix.PosDef.{0, 0} (Fin m) Complex Complex.instRing Complex.partialOrder Complex.instStarRing (A x))
            (@nhds.{u_1} X inst x0) := by sorry
