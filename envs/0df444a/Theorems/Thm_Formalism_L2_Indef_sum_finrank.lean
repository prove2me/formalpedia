-- Prove2me | Theorems.Thm_Formalism_L2_Indef_sum_finrank
-- name    : Formalism.L2.Indef.sum_finrank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:51.283804+00:00
-- url     : https://prove2.me/theorems/f56bed39-da33-460d-80e0-e87c2a5f30e2
-- title:
--   Indef: sum finrank
-- statement:
--   The Indef construction uses the sum finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L39-L49

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

theorem Formalism.L2.Indef.sum_finrank {F V Ix : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Fintype Ix] (A : Ix → Submodule F V) (hi : iSupIndep A) (ht : (⨆ p, A p) = ⊤) :
    ∑ p, finrank F (A p) = finrank F V := by sorry
