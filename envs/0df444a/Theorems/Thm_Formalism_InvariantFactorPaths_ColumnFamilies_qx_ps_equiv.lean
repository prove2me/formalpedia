-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_ps_equiv
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qx_ps_equiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:47.961505+00:00
-- url     : https://prove2.me/theorems/ae05aeb7-2ea3-448e-a8a7-0f85edfe4a31
-- title:
--   Column Families: qx ps equiv
-- statement:
--   The Column Families construction uses the qx ps equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QxPhApply.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QxPhApply.lean#L14-L18

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qx_ps_equiv (hd : IsStripData B be Str ps) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : nu ∈ Str mu)
    (K : TIdx mu) (k : κ) (I : TIdx nu) :
    ∑ y : TIdx mu × κ, TMat mu K y.1 * B k y.2 * (ps mu nu y I : GLCoord ℤ n) =
      ∑ I', (ps mu nu (K, k) I' : GLCoord ℤ n) * TMat nu I' I := by sorry
