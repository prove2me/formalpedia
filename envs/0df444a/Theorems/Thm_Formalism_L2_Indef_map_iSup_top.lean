-- Prove2me | Theorems.Thm_Formalism_L2_Indef_map_iSup_top
-- name    : Formalism.L2.Indef.map_iSup_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:14.216796+00:00
-- url     : https://prove2.me/theorems/82072364-8da7-499d-9fdd-62d24dffbc8e
-- title:
--   Indef: map i Sup top
-- statement:
--   The Indef construction uses the map i Sup top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L71-L76

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

theorem Formalism.L2.Indef.map_iSup_top {F : Type} [Field F] {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) F)
    (h : Function.Bijective φ.mulVec) {Ix : Type} (A : Ix → Submodule F (Fin d → F)) (ht : (⨆ p, A p) = ⊤) :
    (⨆ p, (A p).map φ.mulVecLin) = ⊤ := by sorry
