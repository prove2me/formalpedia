-- Prove2me | Theorems.Thm_Formalism_L2_Indef_ColData_fnorm_eq_zero
-- name    : Formalism.L2.Indef.ColData.fnorm_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:33.596099+00:00
-- url     : https://prove2.me/theorems/46fa10a3-9aaf-421a-8a1c-42c55da57a6f
-- title:
--   Col Data: fnorm eq zero
-- statement:
--   The Col Data construction uses the fnorm eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L451-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L451-L461

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
open Formalism.L2.Indef.ColData
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {S : IndefData Df} (C : ColData Dc Sp S)

theorem Formalism.L2.Indef.ColData.fnorm_eq_zero {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : IsUnit Y.det) (y : Fin n → ℂ) (h : fnorm Y y = 0) : y = 0 := by sorry
