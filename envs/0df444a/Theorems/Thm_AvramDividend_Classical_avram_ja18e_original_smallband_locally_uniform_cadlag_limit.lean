-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18e_original_smallband_locally_uniform_cadlag_limit
-- name    : AvramDividend.Classical.avram_ja18e_original_smallband_locally_uniform_cadlag_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:56:17.326879+00:00
-- url     : https://prove2.me/theorems/9362895e-83e2-47e7-8b1d-a997abd3f017
-- title:
--   Locally uniform original finite-activity compensated jump path limit is right-continuous and starts at zero
-- statement:
--   Use genuine original marked negative jump paths. Proved finite activity ensures a single a.e. event with finitely many negative jumps on every bounded clock (ebd98fb4), Proved original finite-band jump sums identify each cutoff as finite marked right-continuous steps minus deterministic compensator (1c1d4731), and a source quantitative uniform Cauchy modulus 99422ce0 ensures uniform-on-compact convergence; original finite-activity small-jump suppression 035c1c05 assists. Construct the same-space Jsmall path with a.e pointwise cutoff limit, right-continuity at every time, and zero at time zero. No integrability/adaptedness conclusion is needed in this child: those are established independently by Proved original envelope b3763297 and separate  adaptation bridge.
-- source:
--   Single remaining physical path-regularity obligation in reduction of 678e826a and root-connected 23979329.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18e_original_smallband_locally_uniform_cadlag_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (Jsmall t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => Jsmall u ω) (Set.Ici t) t) ∧
      (∀ᵐ ω ∂P, Jsmall 0 ω = 0) := by sorry
