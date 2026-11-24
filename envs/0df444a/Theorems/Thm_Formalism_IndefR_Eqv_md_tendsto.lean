-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_md_tendsto
-- name    : Formalism.IndefR.Eqv.md_tendsto
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:31.297224+00:00
-- url     : https://prove2.me/theorems/7f317674-5e47-4323-931f-291e94eac16d
-- title:
--   Eqv: md tendsto
-- statement:
--   The Eqv construction uses the md tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L103-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L103-L136

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

theorem Formalism.IndefR.Eqv.md_tendsto : ∀ (n : ℕ) (φ : V → ℂ), ContDiff ℝ ∞ φ → ∀ (v : Fin n → V) (a : V) (ε : ℝ), 0 < ε →
    ∃ δ > 0, ∀ h, 0 < h → h < δ → ∀ b, ‖b - a‖ < δ → ‖md φ n v h b - iteratedFDeriv ℝ n φ a v‖ ≤ ε
  := by sorry
