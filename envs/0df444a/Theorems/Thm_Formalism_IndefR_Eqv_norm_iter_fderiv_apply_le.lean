-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_norm_iter_fderiv_apply_le
-- name    : Formalism.IndefR.Eqv.norm_iter_fderiv_apply_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:38.032994+00:00
-- url     : https://prove2.me/theorems/5df1b52a-3e1b-46dc-bad4-0fa7989007d1
-- title:
--   Eqv: norm iter fderiv apply le
-- statement:
--   The Eqv construction uses the norm iter fderiv apply le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L138-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L138-L151

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_NormIterFderivApplyLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
open Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem Formalism.IndefR.Eqv.norm_iter_fderiv_apply_le {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (w y : V) :
    ‖iteratedFDeriv ℝ n (fun z => fderiv ℝ φ z w) y‖ ≤ ‖iteratedFDeriv ℝ (n + 1) φ y‖ * ‖w‖ := by sorry
