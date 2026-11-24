-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_keyZ
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_keyZ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:46.20206+00:00
-- url     : https://prove2.me/theorems/78045a91-de28-4f4c-9b46-b54140a62fa2
-- title:
--   Column Families: qb key Z
-- statement:
--   The Column Families construction uses the qb key Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QbIndepField.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QbIndepField.lean#L39-L49

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_keyZ {M : GLMod n} (CF : ColFam M) (j : CF.J) (I : TIdx (CF.mu j)) (nu : Fin n → ℤ) (i : M.ι) :
    ∑ k, (prMu M nu i k : GLCoord ℤ n) * ∑ l, M.A k l * (CF.ph j l I : GLCoord ℤ n) =
      ∑ K, if qb_wtT (CF.mu j) K = nu then (CF.ph j i K : GLCoord ℤ n) * TMat (CF.mu j) K I else 0 := by sorry
