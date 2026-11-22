-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_compensated_simple_mark_time_additivity_allactivity_20261122
-- name    : AvramDividend.Classical.avram_oai_original_physical_compensated_simple_mark_time_additivity_allactivity_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:58:30.07854+00:00
-- url     : https://prove2.me/theorems/fe0b9d23-9938-46df-9d8b-2a07ea98a4aa
-- title:
--   True original all-activity finite real simple negative marked compensated Lévy process has exact time increment decomposition
-- statement:
--   For the ACTUAL original intrinsic Lévy marked jump measure NX, any locally finite-intensity negative measurable mark set S and finite-range real SimpleFunc g, prove P-almost surely that the true compensated weighted signed fibre sum process F_t decomposes F_t=F_s+G_(s,t) for every deterministic s≤t. This is the critical pathwise stochastic-source bridge from the independently Proved source real negative mark count interval additivity (2de52b33) and the exact real deterministic time compensator arithmetic (c61595e9), synchronised across finite simple mark fibres via Filter.eventually_all_finset. No global finite jump activity, artificial PRM or asserted martingale property. Together with already Proved original right-continuous strong adaptedness c522b292, conditional centred simple-mark increments ec634a99 and true physical L1 per-cell integrability, this permits a direct original process compensated-mark martingale proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_negative_mark_real_count_interval_additivity_allactivity_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_finite_time_mark_real_compensator_additivity_20261122
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_physical_compensated_simple_mark_time_additivity_allactivity_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (hν : X.ν S < ⊤) (g : SimpleFunc ℝ ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let F : ℝ≥0 → Ω → ℝ := fun u ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc 0 u ×ˢ B y)).toReal -
          (((u : ℝ≥0∞) * X.ν (B y))).toReal)
    let G : Ω → ℝ := fun ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc s t ×ˢ B y)).toReal -
          ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B y))).toReal)
    ∀ᵐ ω ∂P, F t ω = F s ω + G ω := by sorry
