-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_step_pointwise_endpoints
-- name    : AvramDividend.Classical.avram_locmoll_band_step_pointwise_endpoints
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:12:22.287173+00:00
-- url     : https://prove2.me/theorems/c61b9724-9214-58a8-a49d-45d8e5fdcaa6
-- title:
--   The actual cell witness converges to prepayment, postpayment and discount on every eligible time
-- statement:
--   The actual cell witness converges to prepayment, postpayment and discount on every eligible time
-- source:
--   Physical dividend step certificate 45e95e97-eef3-4a02-ab5a-913134e1d165

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_step_pointwise_endpoints
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (H θ : ℝ≥0) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (a b c : ℕ → ℝ → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (htθ : t ≤ (θ : ℝ))
    (he : t = 0 ∨ ENNReal.ofReal t < ruinTime X x D ω)
    (h0 : ∀ n, t = 0 → a n t = x ∧ b n t = x - rightLimit D 0 ω ∧ c n t = 1)
    (hpos : ∀ n, 0 < t → ∃ i < m n + 1,
      let l := min ((i : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ
      let r := min (((i + 1 : ℕ) : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ
      (l : ℝ) < t ∧ t ≤ (r : ℝ) ∧
      a n t = x + X.X r ω - rightLimit D l ω ∧
      b n t = (if r = θ ∧ ¬ (r = 0 ∨ (r : ℝ≥0∞) < ruinTime X x D ω)
        then riskProcess X x D r ω else x + X.X r ω - rightLimit D r ω) ∧
      c n t = Real.exp (-(q * (r : ℝ)))) :
    Tendsto (fun n => a n t) atTop (𝓝 (riskProcess X x D t.toNNReal ω)) ∧
    Tendsto (fun n => b n t) atTop (𝓝 (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω)) ∧
    Tendsto (fun n => c n t) atTop (𝓝 (Real.exp (-(q * t)))) := by sorry
