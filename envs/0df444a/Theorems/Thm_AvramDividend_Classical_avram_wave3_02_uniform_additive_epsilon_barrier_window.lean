-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_additive_epsilon_barrier_window
-- name    : AvramDividend.Classical.avram_wave3_02_uniform_additive_epsilon_barrier_window
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T22:20:54.660082+00:00
-- url     : https://prove2.me/theorems/7a2cf678-93ab-4acb-8676-29d30d64ee27
-- title:
--   One finite cap interval approximates all genuine barrier-class optima within a common additive epsilon over bounded capital including zero
-- statement:
--   For every fixed bounded nonnegative starting capital range [0,R], positive discount under Standing and any additive error tolerance ε>0, there exists a single finite barrier cutoff A such that, simultaneously for all 0≤x≤R, the best genuine expected discounted Stieltjes dividend value among all nonnegative constant barriers is bounded above by the best value restricted to barriers in [0,A], plus ε. This is a rigorous uniformly epsilon-accurate finite-search reduction for the actual source Lévy barrier strategy, including zero initial surplus and without assuming barrier-parameter continuity, attainment, global optimality or scale C1.
-- source:
--   Avram Palmowski Pistorius (2007), original spectrally negative Levy constant-barrier value; canonically accepted uniform high-barrier Stieltjes value and epsilon-window lattice reduction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_approximate_finite_barrier_window

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_uniform_additive_epsilon_barrier_window
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 0 ≤ x → x ≤ R →
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) ≤
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a ∧ a ≤ A),
        dividendValue X q x (barrierStrategy X x a)) + ENNReal.ofReal ε := by sorry
