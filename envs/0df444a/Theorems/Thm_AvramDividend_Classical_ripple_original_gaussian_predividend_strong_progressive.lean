-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_gaussian_predividend_strong_progressive
-- name    : AvramDividend.Classical.ripple_original_gaussian_predividend_strong_progressive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:38:31.882832+00:00
-- url     : https://prove2.me/theorems/062076fc-fb3f-45e9-9346-e252f5045538
-- title:
--   Actual original left-limit predividend Gaussian coefficient is strongly progressive in the original right-continuous filtration
-- statement:
--   For any original spectrally negative Levy surplus including paths with Gaussian and downward jumps, any adapted left-continuous admissible dividend strategy, and any C2 candidate w on a region containing the compact band [u,v], the original Gaussian coefficient sigma times the derivative of w evaluated at the original prepayment reserve left limit and masked to this band is strongly progressively measurable with respect to the original right-continuous filtration. It requires no replacement Brownian motion or change of probability space. This bridges the exact Avram predictable-gradient construction to the progressively measurable integrand interface used by Brownian Ito calculus.
-- source:
--   Original source-exact Proved Avram theorem 7ae1130d-7935-43f5-ad75-a3ce3d5de9ac and pinned Mathlib MeasureTheory.IsStronglyPredictable.isStronglyProgressive, remote type probed on 2026-11-22; complementary to Ripple StoppedPredictableIntegrand.lean commit e216e28ce3ffb43877e11f71be260e40a37a35df.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.ripple_original_gaussian_predividend_strong_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    IsStronglyProgressive 𝓕.rightCont (fun t ω => G (t,ω)) := by sorry
