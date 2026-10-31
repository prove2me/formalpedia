-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_approximate_finite_barrier_window
-- name    : AvramDividend.Classical.avram_wave3_02_uniform_approximate_finite_barrier_window
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:16:43.440924+00:00
-- url     : https://prove2.me/theorems/0ac0bc04-deaf-4830-9e09-77734fe60585
-- title:
--   Uniform finite-cap approximation of genuine best-barrier dividend values over all bounded nonnegative reserves, including zero
-- statement:
--   Under Standing and positive discount for the original spectrally negative Lévy source, for any finite capital range [0,R] including the origin and any positive tolerance ε, there is one finite payout cap A≥0 such that the unrestricted supremum of actual expected discounted Stieltjes dividends over all nonnegative constant barriers is no larger than the lattice maximum of the restricted [0,A] supremum and ε for every starting capital x∈[0,R]. Uses the canonically Proved uniform source high-barrier dividend convergence to zero and lattice supremum estimates. This provides an epsilon-accurate uniformly bounded barrier search without assuming continuity/attainment or a strictly positive zero-cap reward at zero surplus.
-- source:
--   Avram Palmowski Pistorius (2007), original stochastic constant-barrier Stieltjes dividend values; source uniform high-barrier vanishing and ENNReal lattice order.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_bounded_reserves_high_barrier_zero

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_uniform_approximate_finite_barrier_window
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 0 ≤ x → x ≤ R →
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) ≤
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a ∧ a ≤ A),
        dividendValue X q x (barrierStrategy X x a)) ⊔ ENNReal.ofReal ε := by sorry
