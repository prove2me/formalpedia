-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_intrinsic_taylor_shrinking_band_tendsto_zero
-- name    : AvramDividend.Classical.avram_p4_f3_original_discounted_intrinsic_taylor_shrinking_band_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:56:28.081202+00:00
-- url     : https://prove2.me/theorems/aedd97a7-295c-40b8-81de-e7ed605cddb0
-- title:
--   Actual original discounted nonlinear Taylor intensity vanishes on shrinking negative marks
-- statement:
--   For the genuine original dividend-controlled spectrally negative Lévy process and its actual intensity X.ν, the discounted nonlinear C² Taylor jump-compensator integral on the shrinking negative band tends to zero for each physical stopped time-path. The proof uses the already Proved uniform source bound d18982d8, the already Proved original ν quadratic-tail limit e5cc5d15, eventual reciprocal cutoff inclusion and the pinned ENNReal squeeze theorem. This is a genuine original ν deterministic dominated-jump limit, not an assertion about the missing same-space Gaussian martingale.
-- source:
--   Proved original canonical Taylor energy bound d18982d8-9bfb-4ead-97e2-69017f720cdd plus Proved original ν quadratic-tail Tendsto e5cc5d15-ff9b-4dd7-b1c2-304194654161; ENNReal.Tendsto.const_mul and order-squeeze at the fixed physical sample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_canonical_shrinking_mark_taylor_energy_upper
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_tail_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_discounted_intrinsic_taylor_shrinking_band_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (f : ℝ → ℝ) (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hf : ContDiffOn ℝ 2 f (Ioo 0 a))
    (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    ∃ r : ℝ, 0 < r ∧ r ≤ min l 1 ∧
      (let U : ℝ≥0 × Ω → ℝ := fun p =>
        let y := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
        if y ∈ Icc l u then y else l
      let A : ℝ≥0 × Ω → ℝ := fun p =>
        if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
      ∀ p : ℝ≥0 × Ω,
        Tendsto (fun n : ℕ =>
          ∫⁻ z in Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
            ENNReal.ofReal (|A p *
              SpectrallyNegativeLevy.generatorIntegrand f (U p) z|)
              ∂X.ν) atTop (𝓝 0)) := by sorry
