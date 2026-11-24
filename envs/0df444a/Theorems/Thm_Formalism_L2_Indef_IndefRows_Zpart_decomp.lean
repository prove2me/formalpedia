-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefRows_Zpart_decomp
-- name    : Formalism.L2.Indef.IndefRows.Zpart_decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:15.847583+00:00
-- url     : https://prove2.me/theorems/a258e66e-b95f-41c1-aab3-7c1ddec9d31a
-- title:
--   Indef Rows: Zpart decomp
-- statement:
--   The Indef Rows construction uses the Zpart decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L166-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L166-L170

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
open Formalism.L2.Indef.IndefRows
variable {Bs : DefBase K} {Df : DefSide Bs} (S : IndefRows Df)
include S

theorem Formalism.L2.Indef.IndefRows.Zpart_decomp (wf : Df.WF) (j : Bs.J) (t : Bs.Tup) :
    iSupIndep (S.Zpart j t) ∧ (⨆ p, S.Zpart j t p) = ⊤ := by sorry
