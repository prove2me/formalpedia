-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefColsR_log_eigenvalue_sum_le_min
-- name    : Formalism.L2.Indef.IndefColsR.log_eigenvalue_sum_le_min
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:35.018998+00:00
-- url     : https://prove2.me/theorems/2d7d0077-51f8-4c27-a93e-cfbab6119903
-- title:
--   Indef Cols R: log eigenvalue sum le min
-- statement:
--   The Indef Cols R construction uses the log eigenvalue sum le min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L328-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L328-L330

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_IndefCols_log_eigenvalue_sum_le_min

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
open Formalism.L2.Indef.IndefColsR
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
  (S : IndefColsR Df Dc Sp N)

theorem Formalism.L2.Indef.IndefColsR.log_eigenvalue_sum_le_min [Nonempty Bs.Ix] (v : InfinitePlace K) :
    ∑ j, N.l6 j ≤ minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) := by sorry
