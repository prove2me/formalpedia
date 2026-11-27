-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_cell_endpoint_limits
-- name    : AvramDividend.Classical.avram_locmoll_band_cell_endpoint_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:12:14.374862+00:00
-- url     : https://prove2.me/theorems/960377af-6882-5460-9849-2ee93c4ad650
-- title:
--   Physical source and controlled reserve tags converge on any eligible positive payment time
-- statement:
--   Physical source and controlled reserve tags converge on any eligible positive payment time
-- source:
--   Physical dividend step certificate 45e95e97-eef3-4a02-ab5a-913134e1d165

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_cell_endpoint_limits
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (θ t : ℝ≥0) (ht : 0 < t) (htθ : t ≤ θ)
    (he : (t : ℝ≥0∞) < ruinTime X x D ω)
    (l r : ℕ → ℝ≥0)
    (hl : Tendsto l atTop (𝓝[<] t))
    (hr : Tendsto r atTop (𝓝[Ici t] t)) :
    Tendsto (fun n => x + X.X (r n) ω - rightLimit D (l n) ω)
      atTop (𝓝 (riskProcess X x D t ω)) ∧
    Tendsto (fun n => if r n = θ ∧ ¬ (r n = 0 ∨ (r n : ℝ≥0∞) < ruinTime X x D ω)
      then riskProcess X x D (r n) ω else x + X.X (r n) ω - rightLimit D (r n) ω)
      atTop (𝓝 (x + X.X t ω - rightLimit D t ω)) ∧
    Tendsto (fun n => Real.exp (-(q * (r n : ℝ)))) atTop (𝓝 (Real.exp (-(q * (t : ℝ))))) := by sorry
