-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_full_interior_negative_mark_kernel_any_cofinal_spatial_mask_integral_converges
-- name    : AvramDividend.Classical.avram_bva_a22_original_full_interior_negative_mark_kernel_any_cofinal_spatial_mask_integral_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:41:45.358199+00:00
-- url     : https://prove2.me/theorems/0f8277d8-0de9-4779-988c-6b2b74337b38
-- title:
--   Actual original full-interior negative-mark source integrals converge along any supplied cofinal spatial bands whenever full marked kernel is genuinely L1
-- statement:
--   For the actual original Lévy process X, dividend D, pre-right-payment reserve at genuine stopped times, negative marks z<0, candidate w, discount q and arbitrary source cofinal positive interior bands, define the exact full stopped interior negative-mark candidate increment and its additional spatially masked integrand. Assume that the full literal kernel is integrable under a measure on the original time-path-mark product and the source masks are measurable. Prove the masked integrals converge to the unmasked full-interior integral along the SAME prescribed cofinal index, without a fast spatial diagonal or artificial replacement process. Pointwise eventual band membership follows from hcover at every original interior source reserve; off the interior support the kernel is zero. Apply the already Proved original masked-kernel dominated convergence theorem. The substantive remaining BVA96 challenge is to prove sufficient full original marked-kernel integrability or control the near-zero/cap spatial tails without assuming an unfounded global generator L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_integrable_original_mark_kernel_eventual_mask_integral_convergence
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_full_interior_negative_mark_kernel_any_cofinal_spatial_mask_integral_converges
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n))
    (S : ℝ≥0) (μ : Measure ((ℝ≥0 × Ω) × ℝ)) :
    let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      Function.leftLim (fun r : ℝ≥0 =>
        x + X.X r ω - rightLimit D r ω) t
    let Interior : Set ((ℝ≥0 × Ω) × ℝ) := {p |
      ((p.1.1 : ℝ≥0∞) ≤
        min (ruinTime X x D p.1.2) (S : ℝ≥0∞) ∧ p.2 < 0) ∧
      (0 < Y p.1.1 p.1.2 ∧
        ENNReal.ofReal (Y p.1.1 p.1.2) < C)}
    let Full : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p ∈ Interior then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1.1 p.1.2 + p.2) - w (Y p.1.1 p.1.2))
      else 0
    let Masked : ℕ → ((ℝ≥0 × Ω) × ℝ) → ℝ := fun n p =>
      if p ∈ Interior ∧ Y p.1.1 p.1.2 ∈ Icc (a n) (b n) then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1.1 p.1.2 + p.2) - w (Y p.1.1 p.1.2))
      else 0
    let E : ℕ → Set ((ℝ≥0 × Ω) × ℝ) := fun n =>
      {p | p ∉ Interior ∨ Y p.1.1 p.1.2 ∈ Icc (a n) (b n)}
    (∀ n, MeasurableSet (E n)) →
    Integrable Full μ →
    Tendsto (fun n => ∫ p, Masked n p ∂μ)
      atTop (𝓝 (∫ p, Full p ∂μ)) := by sorry
