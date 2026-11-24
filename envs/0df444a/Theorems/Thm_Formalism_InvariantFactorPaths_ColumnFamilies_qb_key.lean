-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_key
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:08.222961+00:00
-- url     : https://prove2.me/theorems/eaa163d2-ba2a-4d36-a6e8-b9a5eb7701c4
-- title:
--   Column Families: qb key
-- statement:
--   The Column Families construction uses the qb key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QbIndepField.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QbIndepField.lean#L51-L59

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_key {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] (j : CF.J) (I : TIdx (CF.mu j))
    (nu : Fin n → ℤ) (i : M.ι) :
    qb_ev M F nu (fun i => (CF.vec j I i : F)) i =
      ∑ K, if qb_wtT (CF.mu j) K = nu then (CF.ph j i K : GLCoord F n) * mapCoord F (TMat (CF.mu j) K I)
        else 0 := by sorry
