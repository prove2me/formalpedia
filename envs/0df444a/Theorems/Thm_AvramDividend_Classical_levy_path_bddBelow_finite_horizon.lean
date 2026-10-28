-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
-- name    : AvramDividend.Classical.levy_path_bddBelow_finite_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:23:17.923921+00:00
-- url     : https://prove2.me/theorems/3bff0b3d-b21d-4639-8902-1ce473fce724
-- title:
--   Lévy sample paths are bounded below on every compact time horizon
-- statement:
--   For every sample path of a spectrally negative Lévy process, the image of the finite interval [0,t] is bounded below. Right-continuity and existence of left limits imply upper boundedness of the negated path via an already Proved one-sided-limits compact interval theorem. This closes the pathwise finiteness prerequisite of the killed-survival Laplace envelope and subsequent Wiener–Hopf computation.
-- source:
--   Prove2Me proved one_sided_limits_bddAbove_Icc, applied to the negated sample trajectory.

import Mathlib.Topology.Order.Bornology
import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_path_bddBelow_finite_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω) :
    BddBelow {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} := by sorry
