-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_discounted_negative_kernel_product_ae_bound
-- name    : AvramDividend.Classical.avram_bvb_topcap_original_discounted_negative_kernel_product_ae_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:30:58.766364+00:00
-- url     : https://prove2.me/theorems/b7f7a6c5-d246-4078-889a-bc1aaa27489c
-- title:
--   Original BV top-cap stopped negative-mark kernel has a deterministic product-a.e. bound
-- statement:
--   On the actual original predictable time-P product measure of the finite horizon, and with finite negative Lévy mark intensity, every strict stopped H kernel is bounded in absolute value almost everywhere by one deterministic finite K. The finite-horizon pathwise bound is uniform over original prepayment reserves and negative marks, including zero and ruin; exceptional original P-null paths do not affect the predictable occupation product.
-- source:
--   Necessary topcap L1 kernel domination child for original finite-activity predictable compensator V rate theorem 73b687ec and equality df3fc616. Reuses Proved 6b6d3ac9; needs transfer of P-a.e. full-horizon pre-jump reserve bound through time×P to source predictable μ via hμclock. No cap finite.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_topcap_original_discounted_negative_kernel_product_ae_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCapTop : C = ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμfinite : μ Set.univ < ⊤)
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
        ∀ᵐ p ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))),
          |H n p| ≤ K) := by sorry
