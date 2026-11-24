-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_equiv
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qx_equiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:13.328956+00:00
-- url     : https://prove2.me/theorems/12198f41-61dd-4d7f-9cf4-b214afffebf6
-- title:
--   Column Families: qx equiv
-- statement:
--   The Column Families construction uses the qx equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QxPhApply.lean#L52-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QxPhApply.lean#L52-L82

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxPhApply
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
variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ}
variable {M M' : GLMod n}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qx_equiv (hd : IsStripData B be Str ps) (e : M'.ι ≃ M.ι × κ) (hT : IsTensor M M' B e) (CF : ColFam M)
    (x : qx_J Str CF) (i : M'.ι) (I : TIdx (x.2 : Fin n → ℤ)) :
    ∑ k, M'.A i k * (qx_ph ps e CF x k I : GLCoord ℤ n) =
      ∑ I', (qx_ph ps e CF x i I' : GLCoord ℤ n) * TMat (x.2 : Fin n → ℤ) I' I := by sorry
