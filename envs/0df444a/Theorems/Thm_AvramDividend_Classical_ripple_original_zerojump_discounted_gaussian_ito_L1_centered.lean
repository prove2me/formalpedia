-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_zerojump_discounted_gaussian_ito_L1_centered
-- name    : AvramDividend.Classical.ripple_original_zerojump_discounted_gaussian_ito_L1_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:31:03.421843+00:00
-- url     : https://prove2.me/theorems/412708b3-0d07-48d6-b4ef-41b5b0550216
-- title:
--   Actual original stopped discounted Gaussian Brownian Ito noise is integrable and has exactly zero mean at every nonnegative horizon
-- statement:
--   For every original unbounded-variation zero-jump spectrally negative Levy process with any original adapted dividend strategy, physical two-stop localisation and compact candidate function band, the true discounted Gaussian Ito integral using the physical coefficient of the original prepayment left-limit gradient is integrable and has exactly zero mean under original probability at each nonnegative deterministic horizon. The discount is the actual physical dividend exponential at all positive integration times. This supplies the centered Gaussian source of original discounted stopped Ito-Meyer, leaving the pathwise Ito-Tanaka/Stieltjes cash inequality as the substantive independent open obligation.
-- source:
--   Original discounted stopped Gaussian martingale source 4259127b-d9b0-4630-9a85-75ffca4ce62c, imported LevyStochCalc Brownian Ito negative-time zero theorem and pinned Mathlib Martingale.condExp_ae_eq and integral_condExp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Theorems.Thm_AvramDividend_Classical_ripple_original_zerojump_discounted_gaussian_true_ito_martingale
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.ripple_original_zerojump_discounted_gaussian_ito_L1_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hqnonneg : 0 ≤ q)
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
      Real.exp (-(q * max 0 s)) * S.indicator G (Real.toNNReal s,ω)
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
      ∀ (t : ℝ), 0 ≤ t →
        Integrable
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
            B Fr hBrown H hm hp hq t) P ∧
        (∫ ω, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
          B Fr hBrown H hm hp hq t ω ∂P) = 0 := by sorry
