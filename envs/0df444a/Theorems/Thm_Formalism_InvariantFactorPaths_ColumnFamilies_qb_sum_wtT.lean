-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_sum_wtT
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_sum_wtT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:54.543854+00:00
-- url     : https://prove2.me/theorems/35de9a95-4d1f-429e-aa23-cfa795a61ec2
-- title:
--   Column Families: qb sum wt T
-- statement:
--   The Column Families construction uses the qb sum wt T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean#L65-L72

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_sum_wtT (mu : Fin n → ℤ) (I : TIdx mu) (s : Finset (Fin n)) :
    ∑ b ∈ s, qb_wtT mu I b =
      (s.card : ℤ) * mu (lastIdx n) + ∑ c : ↥(TCols mu), ((s.filter (· ∈ (I c).1)).card : ℤ) := by sorry
