-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_finitecap_fullnegative_stopped_compensator_initial_centered
-- name    : AvramDividend.Classical.avram_freshD_original_finitecap_fullnegative_stopped_compensator_initial_centered
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:43:19.880431+00:00
-- url     : https://prove2.me/theorems/04e002c9-dbbf-4c55-9fb9-dc0b7f638e70
-- title:
--   Original finite-cap entire negative-mark nonlinear stopped compensated source integrable and initially centred
-- statement:
--   For finite negative-jump Lévy activity, bounded stopping time σ and finite cap C, the actual original marked-jump compensated integral of exp(-qt)(w(Y_{t-}+z)-w(Y_{t-})) masked to true nonnegative cap-limited prestate and inclusive original ruin clock is integrable, and has zero integral on every initial-filtration event. NX is the exact original physical jump count and ν its canonical Lévy intensity. Finite activity and cap continuity bound the full value increment, including large ruin overshoots. This is a genuine physical source sub-obligation for the original mixed two-noise cash certificate, not an expected reward assumption.
-- source:
--   Genuine finite-cap original stopped all-negative-mark nonlinear compensator source for Avram Dividend Classical mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43; component of source child avram_freshD_original_mixed_finitecap_fullmark_gaussian_physical_positive_excess. Source uses proved finite-cap uniform mark bound e4637f43 and measurable predictable kernel, compensated count-rate identity, and initial filtration centring.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_finitecap_fullnegative_stopped_compensator_initial_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (n : ℝ))).map Real.toNNReal
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0
    let J : Ω → ℝ := fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    Integrable J P ∧
      ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A, J ω ∂P) = 0 := by sorry
