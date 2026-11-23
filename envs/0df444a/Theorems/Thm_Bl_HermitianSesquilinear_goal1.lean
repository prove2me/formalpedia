-- Prove2me | Theorems.Thm_Bl_HermitianSesquilinear_goal1
-- name    : Bl.HermitianSesquilinear.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:16.696597+00:00
-- url     : https://prove2.me/theorems/9c90aa46-fdcb-4ed4-9d83-cb8a4a902c7b
-- title:
--   Hermitian Sesquilinear: goal1
-- statement:
--   The Hermitian Sesquilinear construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/HermitianSesquilinear/ConjEqOfNonnegReal.lean#L22-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/HermitianSesquilinear/ConjEqOfNonnegReal.lean#L22-L42

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.HermitianSesquilinear

theorem Bl.HermitianSesquilinear.goal1 :
  ∀ {M : Type} [inst : AddCommGroup.{0} M] [inst_1 : Module.{0, 0} Complex M] (Ξ : Formalism.FourierDecayAlt.F7.Sesq M),
  (∀ (m : M),
      And (LE.le.{0} 0 (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ m) m).re)
        (Eq.{1} (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ m) m).im 0)) →
    ∀ (x y : M),
      LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ x) y)) 2)
        (HMul.hMul.{0, 0, 0} (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ x) x).re
          (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ y) y).re) := by sorry
