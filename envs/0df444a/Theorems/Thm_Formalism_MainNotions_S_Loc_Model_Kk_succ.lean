-- Prove2me | Theorems.Thm_Formalism_MainNotions_S_Loc_Model_Kk_succ
-- name    : Formalism.MainNotions.S.Loc.Model.Kk_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:37.523399+00:00
-- url     : https://prove2.me/theorems/87ef515b-e55d-431c-babc-a9df69cfa515
-- title:
--   Model: Kk succ
-- statement:
--   The Model construction uses the Kk succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/FractionFieldToGenericStalkAlgebraMapEq.lean#L254-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/FractionFieldToGenericStalkAlgebraMapEq.lean#L254-L255

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ComplexConjugate
open Formalism Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
open Formalism.MainNotions.S.Loc.Model

theorem Formalism.MainNotions.S.Loc.Model.Kk_succ (M : Model F E) (m : ℕ) (w w' : Pt E (m + 1)) :
    M.Kk (m + 1) w w' = ∑' c : M.Cls m, M.BB w c * conj (M.BB w' c) / (M.nAut c : ℂ) := by sorry
