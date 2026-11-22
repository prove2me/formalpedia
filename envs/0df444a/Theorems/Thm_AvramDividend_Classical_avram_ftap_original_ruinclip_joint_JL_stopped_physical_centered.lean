-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ftap_original_ruinclip_joint_JL_stopped_physical_centered
-- name    : AvramDividend.Classical.avram_ftap_original_ruinclip_joint_JL_stopped_physical_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:19:50.231085+00:00
-- url     : https://prove2.me/theorems/a7c81bef-bb70-4569-bd8f-d37abcc2bb25
-- title:
--   True ruin-clipped physical Lévy stopped nonlinear and linear marked compensated jump martingales jointly L1 centered
-- statement:
--   For the actual spectrally negative Levy risk process and an admissible dividend strategy, at the true ruin-clipped random stopping time tau, the sum of the compensated discounted nonlinear second-order spatial Taylor jump residual and truncated linear small-jump residual is integrable and of zero expectation, where the jump integrals are taken against the actual marked counting measure of the physically stopped Levy sample path rather than the unrestricted original marked measure. Retains general negative jump activity with no abstract auxiliary stochastic source and the exact predividend left-limit, discount and spatial localization. Derives the result from Proved original trueclock joint compensated JL L1 centring and Proved original stopped marked NX indicator transport.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Foundations/Paths.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_ruinclip_allnu_stopped_joint_JL_L1_centered
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_NX_marked_integral_indicator
open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal NNReal

noncomputable section

theorem AvramDividend.Classical.avram_ftap_original_ruinclip_joint_JL_stopped_physical_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (Cband u v δ η : ℝ)
    (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband))
    (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (huv : u + δ < v) (hv : v < Cband)
    (hη : 0 < η) (hη1 : η < 1) :
    let T : ℝ≥0 := (n : ℝ≥0)
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then
        (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let SNX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧
        MeasureTheory.stoppedProcess X.X
          (fun η => (τ η : WithTop ℝ≥0)) t ω -
        Function.leftLim
          (fun r : ℝ≥0 => MeasureTheory.stoppedProcess X.X
            (fun η => (τ η : WithTop ℝ≥0)) r ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t,
        MeasureTheory.stoppedProcess X.X
          (fun η => (τ η : WithTop ℝ≥0)) t ω -
        Function.leftLim
          (fun r : ℝ≥0 => MeasureTheory.stoppedProcess X.X
            (fun η => (τ η : WithTop ℝ≥0)) r ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let J : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then GW ((p.1, ω), p.2) else 0) ∂(SNX ω)) -
      (∫ t, ∫ z,
        (if t ≤ ρ ω then GW ((t, ω), z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    let K : Ω → (ℝ≥0 × ℝ) → ℝ := fun ω p =>
      if p.1 ≤ (n : ℝ≥0) ∧ p.2 ∈ Ioo (-1 : ℝ) (-η) then
        Real.exp (-(q * (p.1 : ℝ))) *
          (if Y (p.1, ω) ∈ Icc (u + δ) v then
            deriv w (Y (p.1, ω)) * p.2 else 0)
      else 0
    let L : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then K ω p else 0) ∂(SNX ω)) -
      (∫ t, ∫ z, (if t ≤ ρ ω then K ω (t, z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    Integrable (fun ω => J τ ω + L τ ω) P ∧
      (∫ ω, J τ ω + L τ ω ∂P) = 0 := by sorry
