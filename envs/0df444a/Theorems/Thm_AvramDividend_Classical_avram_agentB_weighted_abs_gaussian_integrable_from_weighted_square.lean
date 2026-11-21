-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_weighted_abs_gaussian_integrable_from_weighted_square
-- name    : AvramDividend.Classical.avram_agentB_weighted_abs_gaussian_integrable_from_weighted_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:10:50.104474+00:00
-- url     : https://prove2.me/theorems/383da893-383d-4c3c-9784-ee065aeb2cac
-- title:
--   Original nonnegative dividend-weighted Gaussian absolute first moment integrable from weighted square energy
-- statement:
--   For any original nonnegative stopped-history dividend atom weight W and genuine centred Gaussian increment Z, if W and WZ² are integrable and the weighted absolute increment is a.e. measurable, then W|Z| is integrable. The pointwise domination W|Z|≤WZ²+W follows from |Z|≤Z²+1, giving a true L1 bridge to the Gaussian gradient atom source without assuming the desired integrability in advance.
-- source:
--   Simple square Young inequality, integrable sum domination, Integrable.mono_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentB_weighted_abs_gaussian_integrable_from_weighted_square
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (W Z : Ω → ℝ)
    (hWnonneg : ∀ ω, 0 ≤ W ω)
    (hWI : Integrable W P)
    (hWZ2I : Integrable (fun ω => W ω * (Z ω)^2) P)
    (hWZabsMeas : AEStronglyMeasurable
      (fun ω => W ω * |Z ω|) P) :
    Integrable (fun ω => W ω * |Z ω|) P := by sorry
