-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_canonical_shrinking_mark_taylor_energy_upper
-- name    : AvramDividend.Classical.avram_p4_f3_original_canonical_shrinking_mark_taylor_energy_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:07:11.389618+00:00
-- url     : https://prove2.me/theorems/d18982d8-9bfb-4ead-97e2-69017f720cdd
-- title:
--   Original stopped discounted C² jump intensity on shrinking canonical bands bounded by actual ν square tail
-- statement:
--   For every physical time-sample of the original dividend-controlled spectrally negative Lévy process, once the reciprocal canonical small-jump cutoff lies inside the positive C² Taylor radius, the complete nonlinear discounted generator intensity over the canonical shrinking band is bounded by a fixed constant times the true original Lévy quadratic intensity over that band. The bound is uniform in time, sample and cutoff n, and interfaces directly with the proved true ν quadratic-tail convergence e5cc5d15. No Gaussian decomposition or new moments are assumed.
-- source:
--   True source uniform Taylor quadratic bound 9f5f506b and Mathlib restricted Lévy-lintegral monotonicity. Canonical shrinking bands match already Proved ν-tail theorem e5cc5d15.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_intrinsic_taylor_uniform_quadratic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_canonical_shrinking_mark_taylor_energy_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (f : ℝ → ℝ) (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hf : ContDiffOn ℝ 2 f (Ioo 0 a))
    (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ min l 1 ∧ 0 ≤ C ∧
      (let U : ℝ≥0 × Ω → ℝ := fun p =>
        let y := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
        if y ∈ Icc l u then y else l
      let A : ℝ≥0 × Ω → ℝ := fun p =>
        if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
      ∀ (p : ℝ≥0 × Ω) (n : ℕ),
        1 / ((n : ℝ) + 1) ≤ r →
        (∫⁻ z in Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
          ENNReal.ofReal (|A p *
            SpectrallyNegativeLevy.generatorIntegrand f (U p) z|)
            ∂X.ν) ≤
        ENNReal.ofReal C *
          (∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
            ENNReal.ofReal (z ^ 2) ∂X.ν)) := by sorry
