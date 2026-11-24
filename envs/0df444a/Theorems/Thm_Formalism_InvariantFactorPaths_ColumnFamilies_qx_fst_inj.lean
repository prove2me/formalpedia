-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_fst_inj
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qx_fst_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:54.513206+00:00
-- url     : https://prove2.me/theorems/7800a2b9-1552-4d60-8a52-3801f840badb
-- title:
--   Column Families: qx fst inj
-- statement:
--   The Column Families construction uses the qx fst inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QxFstInj.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QxFstInj.lean#L13-L21

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxPhApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxFstInj
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
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ} {M M' : GLMod n}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qx_fst_inj (CF : ColFam M) (nu0 : Fin n → ℤ) (x y : {x : qx_J Str CF // (x.2 : Fin n → ℤ) = nu0})
    (h : x.1.1 = y.1.1) : x = y := by sorry
