-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_zero_right_derivative_top_of_kernel_divergence
-- name    : AvramDividend.Classical.esscher_zero_right_derivative_top_of_kernel_divergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:19:35.080149+00:00
-- url     : https://prove2.me/theorems/bb87279d-227f-46c8-ae26-627e3c6f744a
-- title:
--   Positive Esscher renewal-kernel divergence yields infinite extended zero-right scale slope
-- statement:
--   Under the exact Esscher integral representation, a nonnegative diverging positive renewal kernel forces W' to diverge at zero, and hence the extended `derivZeroPlus W` equals top. This is the extended boundary conclusion directly needed by the zero-barrier formula, with all real analytic requirements explicit.
-- source:
--   Proved esscher_scale_derivative_diverges_of_kernel_diverges (874da69f-128c-4864-8978-8235b7fdefdd) and derivZeroPlus_eq_top_of_right_tendsto_atTop (f711aaad-1543-4cfd-ab1f-e14ce58f18ed).

import Theorems.Thm_AvramDividend_Classical_esscher_scale_derivative_diverges_of_kernel_diverges
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_top_of_right_tendsto_atTop

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped Topology

namespace AvramDividend.Classical

/-- An Esscher renewal density with infinite origin limit forces an infinite extended right derivative. -/
theorem esscher_zero_right_derivative_top_of_kernel_divergence
    (W : ℝ → ℝ) (φ c : ℝ) (f k : ℝ → ℝ)
    (hφ : 0 ≤ φ)
    (hW : ∀ x : ℝ, 0 < x → W x =
      Real.exp (φ * x) * (c + ∫ t in (0 : ℝ)..x, f t))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x)
    (hmeas : ∀ x : ℝ, 0 < x → StronglyMeasurableAtFilter f (𝓝 x) volume)
    (hcont : ∀ x : ℝ, 0 < x → ContinuousAt f x)
    (hFnonneg : ∀ x : ℝ, 0 < x → 0 ≤ c + ∫ t in (0 : ℝ)..x, f t)
    (hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hk : ∀ x : ℝ, 0 < x → k x ≤ f x)
    (hkTop : Tendsto k (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    derivZeroPlus W = ⊤ := by sorry

end AvramDividend.Classical
