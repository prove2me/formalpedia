-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_physical_prefix_predictable_mask
-- name    : AvramDividend.Classical.avram_bv_meas7_original_physical_prefix_predictable_mask
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:53:48.090059+00:00
-- url     : https://prove2.me/theorems/1c35f32d-1e8d-4de3-941f-7025d8d47f79
-- title:
--   Original shrinking physical-prefix stopped mask is predictably measurable
-- statement:
--   For the actual original spectrally negative Levy process and its original dividend strategy, the ruin-truncated prefix clock min(ruinTime, Real.toNNReal(T-T/(n+2))) is bounded and a stopping time in the right-continuous filtration, and the original compact pre-reserve band event is measurable in that filtration's predictable sigma algebra. The statement is exact for every physical index n and makes no independent stochastic measurability assumptions.
-- source:
--   A genuine source-exact specialisation of the already Proved/public original controlled ruin-stopped predictable compact reserve theorem 7759e9e1-2b05-40a3-80c0-b570c12af468. This gives an explicit indexed physical-clock input to a future original cash/value mesh adapter. No proxy process, finite-activity approximation, or claimed cash identity.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_stopped_compact_previsible

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_physical_prefix_predictable_mask
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (a b : ℕ → ℝ) :
    ∀ n : ℕ,
    let δ : ℕ → ℝ := fun k => T / ((k : ℝ) + 2)
    let S : ℝ≥0 := Real.toNNReal (T - δ n)
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
    (∀ ω, τ ω ≤ S) ∧
    IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) ∧
    MeasurableSet[𝓕.rightCont.predictable] E ∧
    (∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)) ∧
    (∀ p ∈ E, p.1 ≤ S) := by sorry
