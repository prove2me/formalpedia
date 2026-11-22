-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_ruinclip_allnu_stopped_joint_JL_L1_centered
-- name    : AvramDividend.Classical.avram_twoagentA_original_ruinclip_allnu_stopped_joint_JL_L1_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T09:34:09.580508+00:00
-- url     : https://prove2.me/theorems/b86345b2-0eba-4330-bfdb-c260908b9427
-- title:
--   Original ruin-clipped nonlinear and annular linear compensator jointly integrable and centred under all Lévy activity
-- statement:
--   For the actual original Levy process X, original right-payment reserve, original truncated ruin time, and arbitrary σ and ν, the stopped nonlinear Taylor marked jump integral and the bounded annular linear mark correction are jointly L1 and have zero mean. The argument applies the proved original stopped nonlinear compensated Taylor source and the genuinely payoff-independent original annular stopped Campbell theorem. No extra payoff integrability, synthetic Poisson random measure, Gaussian-only assumption or finite cap is used. This produces a genuine part of the source martingale needed for the corrected UBV stopped Itô inequality, but does not yet prove the spatial cutoff or full generator/Stieltjes balance.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward26_original_stopped_Taylor_initial_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_canonical_Taylor_initial_event_centered
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_minimal_original_fullnu_annular_stopped_mark_centering
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_twoagentA_original_ruinclip_allnu_stopped_joint_JL_L1_centered
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
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let J : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then GW ((p.1, ω), p.2) else 0) ∂(NX ω)) -
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
      (∫ p, (if p.1 ≤ ρ ω then K ω p else 0) ∂(NX ω)) -
      (∫ t, ∫ z, (if t ≤ ρ ω then K ω (t, z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    Integrable (fun ω => J τ ω + L τ ω) P ∧
      (∫ ω, J τ ω + L τ ω ∂P) = 0 := by sorry
