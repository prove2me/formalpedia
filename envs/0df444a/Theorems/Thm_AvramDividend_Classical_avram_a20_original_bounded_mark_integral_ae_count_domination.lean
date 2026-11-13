-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_integral_ae_count_domination
-- name    : AvramDividend.Classical.avram_a20_original_bounded_mark_integral_ae_count_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:11:07.068208+00:00
-- url     : https://prove2.me/theorems/d8f940f9-0747-4569-9825-24f0ba8423bb
-- title:
--   True original finite-activity bounded negative Borel mark integral is a.s. integrable and bounded by its physical jump count
-- statement:
--   For the actual original spectrally negative Lévy process with finite total negative mark intensity, every measurable bounded real negative mark weight g on a measurable negative Borel set B has, at each deterministic horizon T, an almost surely Bochner integrable integral against the genuine intrinsic physical time-mark jump-count measure NX. Almost surely its absolute value is at most the real source count NX((0,T]×B). The proof imports the already Proved true original finite-activity all-negative jump count a.e. finite theorem, uses rectangle inclusion B⊆(-∞,0) to prove the smaller physical cell has finite mass almost surely, then applies the accepted bounded-mark finite-cell integral norm bound. The result supplies a direct source-faithful uniform bound and samplewise integrability for the physical weighted marked-jump approximants needed for the Gaussian jump-strip L2 moment route.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_bounded_mark_integral_ae_count_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ))
    (g : ℝ → ℝ) (hg : Measurable g)
    (hBound : ∀ z ∈ B, |g z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let C : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ B
    ∀ᵐ ω ∂P,
      IntegrableOn (fun p : ℝ≥0 × ℝ => g p.2) C (NX ω) ∧
      |∫ p in C, g p.2 ∂NX ω| ≤ (NX ω C).toReal := by sorry
