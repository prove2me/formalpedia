-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_native_overshoot_centered_source_bound
-- name    : AvramDividend.Classical.avram_gaussianB_native_overshoot_centered_source_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T21:38:01.580612+00:00
-- url     : https://prove2.me/theorems/1210c5a3-7614-469c-a54d-30aeaf9ca661
-- title:
--   A positive canonical Brownian tube through 17/16000 controls every original stopped Gaussian mesh right endpoint
-- statement:
--   For an original Lévy Gaussian with c=2, a centred source bound through time 17/16000 implies |X_s-sX.c|≤1/4000 at every original physical-grid sample s up to T+Δ, where T=1/1000 and Δ≤1/16000. The horizon is calibrated to the already Proved unconditional native joint Brownian event B186, avoiding a separate event for the overshoot after the stopping horizon.

import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_native_overshoot_centered_source_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → ℝ)
    (hc : X.c = 2)
    (hSource : ∀ s : ℝ≥0, s ≤ (17 / 16000 : ℝ≥0) →
      X.X s ω = B s + 2 * (s : ℝ))
    (hCentered : ∀ s : ℝ≥0, s ≤ (17 / 16000 : ℝ≥0) →
      |B s| ≤ (1 / 4000 : ℝ))
    (Δ : ℝ≥0) (hΔ : Δ ≤ (1 / 16000 : ℝ≥0))
    (s : ℝ≥0) (hs : s ≤ (1 / 1000 : ℝ≥0) + Δ) :
    |X.X s ω - (s : ℝ) * X.c| ≤ (1 / 4000 : ℝ) := by sorry
