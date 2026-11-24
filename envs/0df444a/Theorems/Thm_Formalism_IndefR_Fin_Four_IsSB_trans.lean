-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_trans
-- name    : Formalism.IndefR.Fin.Four.IsSB.trans
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:02.188446+00:00
-- url     : https://prove2.me/theorems/c5795d98-7d01-48b7-8ec3-47bcb79ee860
-- title:
--   Is SB: trans
-- statement:
--   The Is SB construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourExist.lean#L45-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourExist.lean#L45-L61

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {L X : AddSubgroup W}

theorem Formalism.IndefR.Fin.Four.IsSB.trans (hoX : ∀ x ∈ X, ∃ k : ℕ, 0 < k ∧ k • x ∈ L) {Φ : W → ℂ} (h : IsSB L X Φ) {x : W}
    (hx : x ∈ X) : IsSB L X (fun t => Φ (t + x)) := by sorry
