-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_affine_fixed_point_exists
-- name    : AvramDividend.Classical.causal_weighted_BCF_affine_fixed_point_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:21:24.239795+00:00
-- url     : https://prove2.me/theorems/30ad5210-41f5-49a8-ba88-d170a49e7da9
-- title:
--   Existence of a bounded-continuous fixed point for the weighted affine Volterra operator
-- statement:
--   Given a>0, w>0, positive-lag K in L1 and the explicit weighted kernel mass below a, there exists a bounded continuous f on nonnegative times such that its exponentially unweighted version solves the causal derivative-resolvent equation for x>0. Construct an affine strict contraction on BoundedContinuousFunction of nonnegative real time; apply Banach's theorem and undo the weight. This isolates the only unresolved fixed-point construction from the endpoint and primitive regularity already proved.
-- source:
--   Classical Banach contraction principle and proved kernel-mass, continuity, weighted input bounds, and BCF fixed-point helper in this mission.

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_BCF_affine_fixed_point_exists
    (K : ℝ → ℝ) (a β w : ℝ)
    (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    ∃ f : BoundedContinuousFunction ℝ≥0 ℝ,
      ∀ x : ℝ, 0 < x →
        a * (Real.exp (w * x) * f ⟨max x 0, le_max_right x 0⟩) +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) *
              (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩)
              ∂volume) = 1 := by sorry
