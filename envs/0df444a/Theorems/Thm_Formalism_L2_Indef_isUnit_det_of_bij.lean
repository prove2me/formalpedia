-- Prove2me | Theorems.Thm_Formalism_L2_Indef_isUnit_det_of_bij
-- name    : Formalism.L2.Indef.isUnit_det_of_bij
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:05.315064+00:00
-- url     : https://prove2.me/theorems/28c10b0f-97ef-4fe7-962d-cb3823217963
-- title:
--   Indef: is Unit det of bij
-- statement:
--   The Indef construction uses the is Unit det of bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L24-L31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.L2.Indef.isUnit_det_of_bij {F : Type} [Field F] {d : ℕ} (φ : Matrix (Fin d) (Fin d) F)
    (h : Function.Bijective φ.mulVec) : IsUnit φ.det := by sorry
