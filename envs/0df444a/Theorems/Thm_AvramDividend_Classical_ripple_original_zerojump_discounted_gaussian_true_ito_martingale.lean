-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_zerojump_discounted_gaussian_true_ito_martingale
-- name    : AvramDividend.Classical.ripple_original_zerojump_discounted_gaussian_true_ito_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:17:59.93681+00:00
-- url     : https://prove2.me/theorems/4259127b-d9b0-4630-9a85-75ffca4ce62c
-- title:
--   Actual original zero-jump stopped discounted Gaussian Ito integrand yields true filtered martingale
-- statement:
--   For the exact original unbounded-variation zero-jump Levy surplus, original nonanticipating dividend strategy, compact interior candidate w, and original stochastic physical interval (sigma,tau], the genuine discounted Gaussian Ito coefficient e^{-q t} sigma_X times the prepayment left-limit gradient (with q nonnegative) is jointly and progressively measurable, has finite square energy on every positive deterministic Brownian horizon, and its actual completed LevyStochCalc Brownian Ito integral is a true martingale on the original probability space and corresponding filtration. The coefficient e^{-q max(0,t)} matches the original dividend discount e^{-qt} at all contributing nonnegative stochastic-integral times. This result supplies the discounted Gaussian martingale component needed by original stopped Ito-Meyer; it does not assert the still-open signed pathwise cash inequality.
-- source:
--   Proved original same-space two-stop Gaussian Ito martingale e171e5e8-e4e2-4783-b165-37a1f85e6816, Proved progressive joint measurability 26c7a137-ff7e-4d92-abaa-a2730f3a0bb0, pinned imported LevyStochCalc Probability.ProgressivelyMeasurable.mul and ItoL2CompletionMaster.martingale_stochasticIntegralBrownian; Real.exp_le_one_iff for discount contractivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Theorems.Thm_AvramDividend_Classical_ripple_original_zerojump_stopped_gaussian_true_ito_martingale
import Theorems.Thm_AvramDividend_Classical_ripple_LevyStochCalc_progressive_joint_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.ripple_original_zerojump_discounted_gaussian_true_ito_martingale
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
      Martingale
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
          B Fr hBrown H hm hp hq) Fr P := by sorry
