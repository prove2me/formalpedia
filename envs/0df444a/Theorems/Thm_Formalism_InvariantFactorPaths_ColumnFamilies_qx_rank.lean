-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_rank
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qx_rank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:22:24.863589+00:00
-- url     : https://prove2.me/theorems/f669651a-0675-431f-b5cc-ff7f0da08ecb
-- title:
--   Column Families: qx rank
-- statement:
--   The Column Families construction uses the qx rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QxPhApply.lean#L84-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QxPhApply.lean#L84-L89

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qx_rank (hd : IsStripData B be Str ps) (e : M'.ι ≃ M.ι × κ) (CF : ColFam M) :
    Fintype.card M'.ι = ∑ x : qx_J Str CF, dMu (x.2 : Fin n → ℤ) := by sorry
