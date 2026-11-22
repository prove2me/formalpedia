-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefCols_log_eigenvalue_sum_le_min
-- name    : Formalism.L2.Indef.IndefCols.log_eigenvalue_sum_le_min
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:49:02.120982+00:00
-- url     : https://prove2.me/theorems/047f829f-1936-4f4e-bafd-7f0d4d7db79d
-- title:
--   Indef Cols: log eigenvalue sum le min
-- statement:
--   The Indef Cols construction uses the log eigenvalue sum le min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L336-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L336-L339

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

theorem Formalism.L2.Indef.IndefCols.log_eigenvalue_sum_le_min {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
    [Nonempty Bs.Ix] (S : IndefCols Df Dc Sp N) (v : InfinitePlace K) :
    ∑ j, N.l6 j ≤ minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) := by sorry
