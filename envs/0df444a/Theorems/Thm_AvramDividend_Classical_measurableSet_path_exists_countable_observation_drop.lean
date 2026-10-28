-- Prove2me | Theorems.Thm_AvramDividend_Classical_measurableSet_path_exists_countable_observation_drop
-- name    : AvramDividend.Classical.measurableSet_path_exists_countable_observation_drop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:54:12.186622+00:00
-- url     : https://prove2.me/theorems/a45d389a-63a7-42da-9ce5-95027fdb923a
-- title:
--   Existence of a large downward increment among countably many observation pairs is a measurable path event
-- statement:
--   For arbitrary countable index set I and deterministic pairs of observation times u_i,v_i≥0, the set of all real-valued time paths f such that f(u_i)−f(v_i)>r for at least one i is measurable in the coordinate-product σ-algebra. Each finite observation difference is measurable by its two coordinate evaluations, and a countable union remains measurable. This constructs the elementary measurable building block for dyadic/rational path-jump detectors, which are needed to transfer intrinsic càdlàg path events rather than merely canonical Poisson sample-space counts.
-- source:
--   Mathlib Measurable.pi_apply, Measurable.sub, measurableSet_lt, MeasurableSet.iUnion. Foundation for measurable extensions of càdlàg jump events on the full coordinate-product path space.

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.measurableSet_path_exists_countable_observation_drop
    {ι : Type*} [Countable ι]
    (u v : ι → ℝ≥0) (r : ℝ) :
    MeasurableSet {f : (ℝ≥0 → ℝ) | ∃ i : ι, r < f (u i) - f (v i)} := by sorry
