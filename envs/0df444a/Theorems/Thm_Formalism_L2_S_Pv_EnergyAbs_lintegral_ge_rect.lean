-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_lintegral_ge_rect
-- name    : Formalism.L2.S.Pv.EnergyAbs.lintegral_ge_rect
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:25:02.275708+00:00
-- url     : https://prove2.me/theorems/4fdaab0b-cdf0-4d6f-b83a-a720a47cab65
-- title:
--   Energy Abs: lintegral ge rect
-- statement:
--   The Energy Abs construction uses the lintegral ge rect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsLower.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsLower.lean#L14-L27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Measure Filter Topology
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
variable {G : Type} [Group G] [MeasurableSpace G]

theorem Formalism.L2.S.Pv.EnergyAbs.lintegral_ge_rect {μS μS' : Measure G} [SFinite μS'] (f : G → G → ℝ≥0∞)
    (hf : Measurable (fun p : G × G => f p.1 p.2)) (E E' : Set G) (c : ℝ≥0∞)
    (h : ∀ s ∈ E, ∀ s' ∈ E', c ≤ f s s') : c * μS' E' * μS E ≤ ∫⁻ s, ∫⁻ s', f s s' ∂μS' ∂μS := by sorry
