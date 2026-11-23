-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_contDiff_fderiv_apply
-- name    : Formalism.IndefR.Eqv.contDiff_fderiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:19:06.910666+00:00
-- url     : https://prove2.me/theorems/e87ff509-3c3e-4f63-a41c-e517f05051f4
-- title:
--   Eqv: cont Diff fderiv apply
-- statement:
--   The Eqv construction uses the cont Diff fderiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L56-L57

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

theorem Formalism.IndefR.Eqv.contDiff_fderiv_apply {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ) (w : V) : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y w) := by sorry
