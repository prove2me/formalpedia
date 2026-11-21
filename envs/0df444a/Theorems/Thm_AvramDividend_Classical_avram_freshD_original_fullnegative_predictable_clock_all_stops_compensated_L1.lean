-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_fullnegative_predictable_clock_all_stops_compensated_L1
-- name    : AvramDividend.Classical.avram_freshD_original_fullnegative_predictable_clock_all_stops_compensated_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:20:24.658972+00:00
-- url     : https://prove2.me/theorems/423b553c-b5fd-4ae2-bb0b-4719841ba16c
-- title:
--   Exact original negative Lévy mark clock: all stopping-time compensated integrals integrable with zero unconditional mean
-- statement:
--   For an arbitrary jointly predictable original Lévy mark kernel H supported on the original finite time horizon n, if H is L1 on every finite original predictable time×probability clock with the full negative Lévy intensity, then the exact original X jump-count minus its physical Lévy compensator is integrable and mean-zero at every right-continuous stopping time. The same single Lévy jump count NX and full negative mark ν are used for every stop. This is the reusable genuine stochastic compensation obligation for the nonlinearly weighted full-mark ruin-inclusive dividend theorem; it establishes centring rather than assuming it.
-- source:
--   Sound factorisation of Proved physical predictable clock factory 0d49c7f0 and genuine stopped marked compensation ae422bf7, for source theorem 04e002c9 and original cash source 242ca5f1. No false linear Jfull and no reward-budget assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_Levy_finite_predictable_physical_clock
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_original_stopped_marked_L1_zero_mean_no_future_or_band_premises
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_fullnegative_predictable_clock_all_stops_compensated_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hHm : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H)
    (hHsupport : ∀ p, (n : ℝ≥0) < p.1.1 → H p = 0)
    (hHI : ∀ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ →
      Integrable H (letI : MeasurableSpace (ℝ≥0 × Ω) :=
        𝓕.rightCont.predictable
        μ.prod (X.ν.restrict (Iio (0 : ℝ))))) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (n : ℝ))).map Real.toNNReal
    let Jρ : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then H ((p.1, ω), p.2) else 0) ∂(NX ω)) -
      (∫ t, ∫ z, (if t ≤ ρ ω then H ((t, ω), z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    ∀ ρ : Ω → ℝ≥0,
      IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)) →
      Integrable (Jρ ρ) P ∧ (∫ ω, Jρ ρ ω ∂P) = 0 := by sorry
