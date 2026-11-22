-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefCore_fun1
-- name    : Formalism.L2.Indef.IndefCore.fun1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:22.669468+00:00
-- url     : https://prove2.me/theorems/fd666a23-4f88-417a-a386-58103e148a4e
-- title:
--   Indef Core: fun1
-- statement:
--   The Indef Core construction uses the fun1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L441-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L441-L443

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
open Formalism.L2.Indef.IndefCore
variable {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}
  (P : IndefCore Df0 Df1 Dc Sp N)
include P

theorem Formalism.L2.Indef.IndefCore.fun1 (hde : 0 ≤ N.de) (hde3 : N.de ≤ 1 / 3) :
    P.cols.muMaxRR ≤ N.hh - meanLog P.cols.κ + 14 * N.la := by sorry
