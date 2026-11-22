-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_monoWtGe_rad
-- name    : Formalism.DworkPowerSeriesWeights.asmR_monoWtGe_rad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:44:38.252936+00:00
-- url     : https://prove2.me/theorems/9bef48cf-224e-4cb0-a402-d1c08bc7bd9e
-- title:
--   Dwork Power Series Weights: asm R mono Wt Ge rad
-- statement:
--   The Dwork Power Series Weights construction uses the asm R mono Wt Ge rad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmRDotAddRight.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmRDotAddRight.lean#L40-L50

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.asmR_monoWtGe_rad {K : Type u} [NormedField K] {ι : Type v} {pi : ℝ} (h0 : 0 < pi)
    (h1 : pi ≤ 1) {r r' : ι → ℝ} (hr : ∀ i, r i ≤ r' i) {w : ℝ} {n : ι →₀ ℕ} {c : K}
    (h : MonoWtGe pi r w n c) : MonoWtGe pi r' w n c := by sorry
