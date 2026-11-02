-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomly_stopped_discounted_source_product_L1_L2_energy
-- name    : AvramDividend.Classical.avram_wave6_04_actual_randomly_stopped_discounted_source_product_L1_L2_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:01:56.818231+00:00
-- url     : https://prove2.me/theorems/05ef358b-d7cd-4ecf-b024-6a755d36a2a9
-- title:
--   Randomly stopped discounted actual source nonlinear C² Taylor kernel has full negative-mark physical L¹/L² energy
-- statement:
--   At the actual spectrally negative Lévy source X and controlled prepayment reserve Y=leftLim(x+X.X-rightLimit D), with genuine ruinTime and negative-extended interior C² test w, every right-continuous original stopping time τ and finite T produce a q≥0 discounted inclusive stop weight 1_{s≤T} exp(-qs) 1_{s≤τ} bounded by one. The full true negative Lévy-mark product physical predictable clock has finite absolute first and squared energies for the weighted actual compensated Taylor kernel, without assuming first moment of the large negative marks, atomlessness at ruin, a source martingale isometry, or the original source hFuture intensity law. Exact source jump-literal expectation is a different, already Proved conditional theorem.
-- source:
--   Avram Wave6 Chat04 mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. New physical product random-stop L1/L2 generator compensation energy from accepted source products 955eaa85 and 2d67e34c and weight 7b979a09; independent of Chat01 hFuture and Chat02 isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_randomly_stopped_discounted_source_product_L1_L2_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (T : ℝ≥0) (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (q : ℝ) (hq : 0 ≤ q) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0) *
      (if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0)
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
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal (|GW p|)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal ((GW p) ^ 2)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) := by sorry
