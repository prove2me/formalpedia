-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_dvrOfStd_sq
-- name    : Formalism.MainNotions.G.dvrOfStd_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:00.516525+00:00
-- url     : https://prove2.me/theorems/92f5f9d5-4025-40e2-be86-a0de09b92b9f
-- title:
--   G: dvr Of Std sq
-- statement:
--   The G construction uses the dvr Of Std sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ObjBridge.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ObjBridge.lean#L39-L42

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjBridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G

theorem Formalism.MainNotions.G.dvrOfStd_sq {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w) :
    (dvrOfStd h).SqP := by sorry
