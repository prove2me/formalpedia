-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_separated_simple_mark_rightcont_conditional_increment_zero_20261122
-- name    : AvramDividend.Classical.avram_oai_original_physical_separated_simple_mark_rightcont_conditional_increment_zero_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:28:36.316605+00:00
-- url     : https://prove2.me/theorems/a4622167-70ed-469c-b531-0728de55550a
-- title:
--   Actual intrinsic negative Borel simple real-mark compensated time increment has right-continuous past conditional mean zero for any finite local intensity
-- statement:
--   For the ACTUAL intrinsic marked-jump measure of any spectrally negative Lévy process (including infinite global negative jump activity), each finite-range real simple mark g on a measurable local finite-intensity negative Borel S gives a time increment from s to t of its weighted centred physical mark counts with zero conditional expectation given the right-continuous past F_s. The hypotheses include a standard near-s sequence r_k between s and t used in the existing Proved physical first-order Markov/Levy source proof; they do not assert independence synthetically. Prove by taking finite fibre partition S∩{g=y}, establishing each fibre Borel and locally finite intensity from ν(S), establishing actual original count measurability with Proved intrinsic rectangle source theorem d9c55240, then applying Proved original finite simple mark conditional centring avram_anoise17. This is a significant all-activity source-level conditional signed compensated marked-jump increment lemma, needed to prove physical mark process martingality from the exact real mark isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_finite_simple_mark_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_physical_separated_simple_mark_rightcont_conditional_increment_zero_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (r : ℕ → ℝ≥0)
    (hsr : ∀ k, s < r k) (hrt : ∀ k, r k ≤ t)
    (hShort : Tendsto (fun k => r k - s) atTop (𝓝 0))
    (hLong : Tendsto (fun k => t - r k) atTop (𝓝 (t - s)))
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
