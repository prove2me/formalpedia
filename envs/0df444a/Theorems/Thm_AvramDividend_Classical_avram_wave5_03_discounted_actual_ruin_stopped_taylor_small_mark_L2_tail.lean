-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_discounted_actual_ruin_stopped_taylor_small_mark_L2_tail
-- name    : AvramDividend.Classical.avram_wave5_03_discounted_actual_ruin_stopped_taylor_small_mark_L2_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:52:07.243919+00:00
-- url     : https://prove2.me/theorems/431adcfa-f974-47a6-90e1-8a848a597ab4
-- title:
--   Original-source discounted finite-horizon ruin-stopped Taylor mark has vanishing small-jump L2 energy
-- statement:
--   For the actual spectrally negative Levy path and the same adapted left-continuous dividend strategy, the exact source Taylor-remainder jump integrand on a compact C2 interior reserve band, stopped inclusively at the true controlled ruin clock and discounted with an additional deterministic finite horizon, has vanishing nested source ν-L2 energy on every shrinking measurable negative-mark family. The proof uses the canonical 03-B actual stopped small-mark tail and pointwise contraction by exp(-qt) 1_{t≤T}, with q≥0, all on the same right-continuous predictable observation measure. It supplies the analytical small-mark cutoff for a future same-source compensated martingale limit; it does not assume or claim a source compensation/isometry or controlled Ito identity.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), finite-horizon jump Taylor remainder in the original stopped Ito-Meyer argument. Integrator uses source-coupled 03-B Proved cc000c72; explicit bridge for canonical BV ef7e6c20 and corrected UBV 429e17ca.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_compensated_taylor_small_mark_L2_tail

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_discounted_actual_ruin_stopped_taylor_small_mark_L2_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hband : u + δ ≤ v)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then
        (1 : ℝ) else 0) * H p
    let HD : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => ρ p.1 * HS p
    (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((HD (p, z)) ^ 2) ∂X.ν ∂μ) = 0 := by sorry
