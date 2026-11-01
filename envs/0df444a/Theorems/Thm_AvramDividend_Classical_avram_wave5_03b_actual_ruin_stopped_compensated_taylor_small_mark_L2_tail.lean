-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_compensated_taylor_small_mark_L2_tail
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_compensated_taylor_small_mark_L2_tail
-- status  : Open
-- author  : @WillR
-- created : 2026-11-01T01:19:43.586794+00:00
-- url     : https://prove2.me/theorems/cc000c72-532c-4058-9964-28b4fe4889e6
-- title:
--   Actual ruin-stopped compensated source jump Taylor kernel has vanishing small-mark quadratic tails
-- statement:
--   For the literal spectrally negative Lévy source X and the same adapted dividend strategy, the Taylor-compensated nonlinear negative-jump kernel of the actual prepayment left-limit reserve, stopped at its controlled ruin time and localised to a compact strict interior reserve band, has quadratic Lévy-intensity energy tending to zero on every decreasing measurable family of negative mark sets with empty intersection. The uniform source quadratic envelope and actual ν-energy replace any first absolute moment assumption. This proves the L² analytic cutoff of the actual source jump correction, but makes no unproved martingale or compensator claim.
-- source:
--   Exact source X and adapted D. Proved C² full negative-mark Taylor envelope c02ee5a4-a76f-4515-b0fa-d5f8ea9d26aa; actual ruin stopping time and stopped L² b62df142-de27-4678-9eb2-f357de1c687d; Lévy truncation energy X.ν_integrable; generic decreasing marked-energy tail 03134e86-e6de-49ec-8d59-26afc753df00. No abstract independent PRM and no unproved original-source rectangle compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_compensated_taylor_small_mark_L2_tail
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
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
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
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((HS (p, z)) ^ 2) ∂X.ν ∂μ) = 0 := by sorry
