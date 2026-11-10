-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward27_original_stopped_Taylor_with_nonpositive_drift_initial_budget
-- name    : AvramDividend.Classical.avram_pj_reward27_original_stopped_Taylor_with_nonpositive_drift_initial_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:34:46.749167+00:00
-- url     : https://prove2.me/theorems/d93a973e-ff48-4a0b-8646-000a601f1424
-- title:
--   Original stopped compensated Taylor source plus nonpositive integrable HJB drift has initial-filtration conditional budget
-- statement:
--   For Avram's original stopped, compact discounted Taylor compensated jump J at any right-continuous stopping time and any integrable nonpositive original drift B, establish integrability of J+B and conditional expectation E[J+B | F.rightCont 0]≤0 a.s. This joins the newly Proved physical initial-filtration centering 48b7f1e0 to a separate HJB signed drift, while retaining the genuine original source and clock. The remaining physical Itô/dividend ledger is separate.
-- source:
--   Source-specific initial conditional signed budget from Proved pj-reward26 and monotonicity/linearity of conditional expectation. Essential bridge to conditional stopped reward 05ac0c40, but it does not assert unproved physical pathwise Ito equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward26_original_stopped_Taylor_initial_condexp_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward27_original_stopped_Taylor_with_nonpositive_drift_initial_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
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
    ∀ (σ : Ω → ℝ≥0)
      (hσ : IsStoppingTime 𝓕.rightCont
        (fun ω => (σ ω : WithTop ℝ≥0)))
      (B : Ω → ℝ) (hBI : Integrable B P)
      (hBnonpos : ∀ᵐ ω ∂P, B ω ≤ 0),
      Integrable (fun ω => J σ ω + B ω) P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P (fun ω => J σ ω + B ω) ω ≤ 0)
    := by sorry
