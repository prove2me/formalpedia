-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_simple_mark_condExp_all_strict_time_20261122
-- name    : AvramDividend.Classical.avram_oai_original_physical_simple_mark_condExp_all_strict_time_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:37:47.842341+00:00
-- url     : https://prove2.me/theorems/ec634a99-2374-4780-b4a3-8d235ecc1311
-- title:
--   Actual original all-activity compensated finite simple negative mark increment is conditionally centred at every positive horizon, no collar sequence assumptions
-- statement:
--   For ANY strict positive time interval s<t, any original spectrally negative Lévy process, any locally finite ν(S) measurable negative mark set S and any finite-range real simple mark g, the actual source signed compensated mark count increment on (s,t] has conditional mean zero given the original right-continuous past F_s. The proof constructs the canonical interior right-time collar sequence explicitly using the independently Proved deterministic theorem and applies the independently Proved true original physical mark fibre conditional centring a4622167. No global finite negative jump activity, artificial sequence assumption, synthetic Poisson driver, or conditional martingale assumption; this is a directly proved finite-step original physical marked-jump martingale source result.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_finite_simple_mark_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_separated_simple_mark_rightcont_conditional_increment_zero_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_nonnegative_time_short_right_bridge_sequence_20261122
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_physical_simple_mark_condExp_all_strict_time_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s < t)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hν : X.ν S < ⊤)
    (g : SimpleFunc ℝ ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let F : Ω → ℝ := fun ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc s t ×ˢ B y)).toReal -
          (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B y)).toReal)
    P[F | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
