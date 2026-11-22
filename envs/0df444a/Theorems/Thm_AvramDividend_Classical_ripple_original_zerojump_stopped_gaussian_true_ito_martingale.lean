-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_zerojump_stopped_gaussian_true_ito_martingale
-- name    : AvramDividend.Classical.ripple_original_zerojump_stopped_gaussian_true_ito_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:05:28.624467+00:00
-- url     : https://prove2.me/theorems/e171e5e8-e4e2-4783-b165-37a1f85e6816
-- title:
--   Original zero-jump predividend two-stop Gaussian integrand has a genuine centred Brownian Ito martingale with original filtered driver
-- statement:
--   For the original unbounded-variation zero-jump spectrally negative Levy process, with any adapted dividend strategy and actual physical stopping times sigma and tau, construct on the original sample space a real-time filtered Brownian motion exactly equal to the original normalised Levy surplus. The actual sigma_X times derivative of the candidate function at the prepayment left-limit reserve, masked to an interior compact band and the original random two-stopping-time interval, is jointly measurable, progressively measurable with respect to that Brownian filtration, and square integrable on all positive real horizons. Its actual LevyStochCalc completed Brownian Ito integral is a genuine filtered martingale. This is the Gaussian source stochastic witness of original stopped Ito-Meyer, retaining original X, P, D, clock and filtration; the signed discounted Stieltjes cash upper bound remains a separate source obligation.
-- source:
--   Original Brownian driver e72d0175-b6bd-45bf-ad30-0049fa7ed69a; Proved full real progressive stopped source 3616d901-22f3-462f-b3f8-6e1422d0fd3d; Proved original all-time Gaussian energy 27c1caa4-0ed0-47d4-af9f-6ef9e27d19f2; generic joint-measurability bridge 26c7a137-ff7e-4d92-abaa-a2730f3a0bb0; original imported LevyStochCalc Brownian ItoL2CompletionMaster source martingale_stochasticIntegralBrownian.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Theorems.Thm_AvramDividend_Classical_ripple_original_zerojump_real_Brownian_stopped_progressive_L2
import Theorems.Thm_AvramDividend_Classical_ripple_original_stopped_gaussian_real_all_horizon_energy
import Theorems.Thm_AvramDividend_Classical_ripple_LevyStochCalc_progressive_joint_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.ripple_original_zerojump_stopped_gaussian_true_ito_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) (σ τ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      X.σ * (if Y p ∈ Icc u v then deriv w (Y p) else 0)
    let S : Set (ℝ≥0 × Ω) := {p | 0 < p.1 ∧
      (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
      (p.1 : WithTop ℝ≥0) ≤ τ p.2}
    let H : Ω → ℝ → ℝ := fun ω s =>
      S.indicator G (Real.toNNReal s,ω)
    ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
      (Fr : Filtration ℝ mΩ)
      (hFr : ∀ t : ℝ, Fr t = 𝓕.rightCont (Real.toNNReal t))
      (hBrown : LevyStochCalc.Brownian.IsBrownianFiltration B Fr)
      (hB : ∀ (t : ℝ) (ω : Ω), B.W t ω =
        (X.X (Real.toNNReal t) ω -
          (Real.toNNReal t : ℝ) * X.c) / X.σ)
      (hτFr : IsStoppingTime Fr
        (fun ω => ((τ ω : ℝ) : WithTop ℝ)))
      (hm : Measurable (Function.uncurry H))
      (hp : LevyStochCalc.Probability.ProgressivelyMeasurable Fr H)
      (hq : ∀ (t : ℝ), 0 < t →
        ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) t,
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      Martingale
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
          B Fr hBrown H hm hp hq) Fr P := by sorry
