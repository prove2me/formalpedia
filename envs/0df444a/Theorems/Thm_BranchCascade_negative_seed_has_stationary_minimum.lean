-- Prove2me | Theorems.Thm_BranchCascade_negative_seed_has_stationary_minimum
-- name    : BranchCascade.negative_seed_has_stationary_minimum
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:51:18.582395+00:00
-- url     : https://prove2.me/theorems/50be4e31-be7e-456c-8962-cabb6c6464c0
-- title:
--   Negative seed attains an interior stationary minimum
-- statement:
--   Let f be continuous on [a,b] and differentiable on (a,b). If a<x<b and f(x)<min(0,f(a),f(b)), then there exists u in (a,b) with f(u)<0 and f′(u)=0. This is the compact-minimum step of the negative cascade.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchCascade.negative_seed_has_stationary_minimum     (f : ℝ → ℝ) (a b x : ℝ)
    (hax : a < x) (hxb : x < b) (hx : f x < 0)
    (ha : f x < f a) (hb : f x < f b)
    (hc : ContinuousOn f (Icc a b))
    (hd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ u ∈ Ioo a b, f u < 0 ∧ deriv f u = 0 := by sorry
