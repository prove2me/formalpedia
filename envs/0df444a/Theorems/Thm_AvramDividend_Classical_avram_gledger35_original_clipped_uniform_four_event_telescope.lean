-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger35_original_clipped_uniform_four_event_telescope
-- name    : AvramDividend.Classical.avram_gledger35_original_clipped_uniform_four_event_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:58:33.385649+00:00
-- url     : https://prove2.me/theorems/5d82cfe2-572f-4b90-8665-014bfb8c6321
-- title:
--   Original stopped uniform-grid four-event Itô and prepayment dividend telescope
-- statement:
--   Specialise the proved original stochastic four-event exact dividend/reward identity to the finite uniform mesh v_i=min(i*n/(m+1),ρ) of the Gaussian-32 compact stopped ledger. The clock is bounded by the original ruin time and n. This gives the exact original postpayment, prepayment, time-discount and terminal-right-payment correction identity, with no independent auxiliary process or numerical approximation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger35_original_clipped_uniform_four_event_telescope {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ) (n m : ℕ) (ρ : Ω → ℝ≥0) (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0)) (ω : Ω) : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω); let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω; let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω; E (ρ ω) * w (riskProcess X x D (ρ ω) ω) = w x + (w (x - rightLimit D 0 ω) - w x) + (∑ i ∈ Finset.range (m + 1), ((E (v (i + 1)) - E (v i)) * w (Y (v i)) + E (v (i + 1)) * (w (Z i) - w (Y (v i))) + E (v (i + 1)) * (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) + E (v (i + 1)) * (w (Y (v (i + 1))) - w (riskProcess X x D (v (i + 1)) ω)))) + E (ρ ω) * (w (riskProcess X x D (ρ ω) ω) - w (Y (ρ ω))) := by sorry
