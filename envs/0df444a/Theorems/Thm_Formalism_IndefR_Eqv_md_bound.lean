-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_md_bound
-- name    : Formalism.IndefR.Eqv.md_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:03.114905+00:00
-- url     : https://prove2.me/theorems/c619ece4-e02f-4d4e-a9f7-51b0b7640f5d
-- title:
--   Eqv: md bound
-- statement:
--   The Eqv construction uses the md bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L153-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L153-L178

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

theorem Formalism.IndefR.Eqv.md_bound : ∀ (n : ℕ) (φ : V → ℂ), ContDiff ℝ ∞ φ → ∀ (v : Fin n → V) (h : ℝ), 0 < h → ∀ (b : V) (M : ℝ),
    (∀ y, ‖y - b‖ ≤ h * ∑ i, ‖v i‖ → ‖iteratedFDeriv ℝ n φ y‖ ≤ M) → ‖md φ n v h b‖ ≤ M * ∏ i, ‖v i‖
  := by sorry
