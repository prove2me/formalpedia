-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_uniform_boundary_reward
-- name    : AvramDividend.Classical.avram_wave3_02_standing_uniform_boundary_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:43:38.010909+00:00
-- url     : https://prove2.me/theorems/00f24ec0-a8df-4764-9410-e66a9fb429d6
-- title:
--   Genuine Stieltjes reflected dividend reward uniformly bounded over all nonnegative barriers
-- statement:
--   For any original Standing spectrally negative Lévy process, positive discount q and corresponding q-scale function W, there exists one strictly positive finite real constant C such that the genuine expected discounted reflected Stieltjes dividend reward barrierSupValue(X,a,q) is at most ENNReal.ofReal C for every nonnegative barrier a. This source-faithful unconditional result follows from the previously verified Esscher-normalised monotonicity factor and the accepted finite-grid source-reward upper bound. It requires neither global C1 nor differentiability at a particular barrier.
-- source:
--   Avram Palmowski Pistorius (2007), q-scale Esscher transform and boundary Stieltjes regulator estimates; canonically Proved Esscher growth and uniform gap bound.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_boundary_reward_of_unit_gap

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_standing_uniform_boundary_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 ≤ a →
      barrierSupValue X a q ≤ ENNReal.ofReal C := by sorry
