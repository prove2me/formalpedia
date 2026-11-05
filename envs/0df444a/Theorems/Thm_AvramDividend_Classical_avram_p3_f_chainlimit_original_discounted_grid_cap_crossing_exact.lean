-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_discounted_grid_cap_crossing_exact
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_grid_cap_crossing_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:13:38.255195+00:00
-- url     : https://prove2.me/theorems/e8f33c1f-8c64-41db-9e33-1d525fda5f21
-- title:
--   Exact discounted original source-frozen C1 grid correction at finite cap crossings
-- statement:
--   For the genuine original spectrally negative Levy source X.X, actual right-payment control D, and physical discount exp(-q u_i), the full finite-grid sum of frozen V increments equals the corresponding frozen w increments plus a single explicit original cap-crossing correction sum. This corrects the strict-grid budget's cap-safe hVSource hypothesis without excluding true above-cap source excursions. Cap contact and infinite cap make the correction zero. No stochastic compensation, stopped chain conclusion or hidden HJB equality is assumed.
-- source:
--   Accepted Proved original cap source crossing correction 84f8df8a-bc5d-46ee-b78e-82e9c1fc85d2, genuine X.X, rightLimit D and original discounted grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_grid_cap_crossing_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (u : ℕ → ℝ≥0) (n : ℕ) :
    ∀ ω,
      let a : ℕ → ℝ := fun i =>
        x + X.X (u i) ω - rightLimit D (u i) ω
      let b : ℕ → ℝ := fun i =>
        x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
      let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
      let κ : ℕ → ℝ := fun i =>
        if C = ⊤ then 0
        else if b i ≤ C.toReal then 0
        else w C.toReal + (b i - C.toReal) - w (b i)
      (∑ i ∈ Finset.range n, e i * (V (b i) - V (a i))) =
        (∑ i ∈ Finset.range n, e i * (w (b i) - w (a i))) +
        (∑ i ∈ Finset.range n, e i * κ i) := by sorry
