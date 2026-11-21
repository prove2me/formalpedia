-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_true_stopped_discount_fullnegative_value_product_predictable
-- name    : AvramDividend.Classical.avram_freshD_original_true_stopped_discount_fullnegative_value_product_predictable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:34:41.429461+00:00
-- url     : https://prove2.me/theorems/81b48a83-f3f6-4841-84c4-4eccf636e919
-- title:
--   Genuine original ruin- and stopping-time-masked discounted full nonlinear value-increment core is jointly predictable for every negative Lévy mark
-- statement:
--   The product of the genuine original bounded-horizon σ-stopped discounted weight and the original ruin-clipped full nonlinear negative-mark value increment w(Y_{t-}+z)-w(Y_{t-}) is measurable for the right-continuous predictable time×path filtration and real-mark space. It retains all negative marks and the inclusive ruin mark, and is valid without a cap assumption. It supplies the exact marked source core required in the original finite-cap fullmark compensation, separate from the closed-cap state mask and the pointwise physical H identity.
-- source:
--   Valid strong predictable marked kernel source to b7420f09 and 242ca5f1. Reuses Proved af8a1cbf original ruin masked nonlinear marked kernel, 7b979a09 stopped discount weight, and exact original Lévy and dividend strategy definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_controlled_stopped_prejump_marked_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_true_stopped_discount_fullnegative_value_product_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        ((if p.1.1 ≤ (n : ℝ≥0)
            then Real.exp (-(q * (p.1.1 : ℝ))) else 0) *
          (if (p.1.1 : ℝ≥0∞) ≤ (σ p.1.2 : ℝ≥0∞)
            then (1 : ℝ) else 0)) *
          ((if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2
            then (1 : ℝ) else 0) *
           (w (Y p.1 + p.2) - w (Y p.1)))) := by sorry
