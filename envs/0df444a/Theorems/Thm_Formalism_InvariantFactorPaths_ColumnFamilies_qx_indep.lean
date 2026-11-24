-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_indep
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qx_indep
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:22:15.797861+00:00
-- url     : https://prove2.me/theorems/a2bbf571-e0a0-4cef-bc75-0a8afcc2b76c
-- title:
--   Column Families: qx indep
-- statement:
--   The Column Families construction uses the qx indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QxFstInj.lean#L23-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QxFstInj.lean#L23-L84

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qx_indep (hd : IsStripData B be Str ps) (e : M'.ι ≃ M.ι × κ) (CF : ColFam M) (F : Type) [Field F]
    (nu0 : Fin n → ℤ) :
    LinearIndependent F (fun x : {x : qx_J Str CF // (x.2 : Fin n → ℤ) = nu0} =>
      fun i => ((qx_ph ps e CF x.1 i (canT (x.1.2 : Fin n → ℤ)) : ℤ) : F)) := by sorry
