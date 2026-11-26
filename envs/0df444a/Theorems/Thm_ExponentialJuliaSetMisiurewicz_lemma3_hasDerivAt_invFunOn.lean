-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma3_hasDerivAt_invFunOn
-- name    : ExponentialJuliaSetMisiurewicz.lemma3_hasDerivAt_invFunOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:12.015031+00:00
-- url     : https://prove2.me/theorems/456d946c-d5a0-5ef4-aef7-48d737f116c7
-- title:
--   Exponential Julia Set Misiurewicz: lemma3 has Deriv At inv Fun On
-- statement:
--   The inverse of an injective holomorphic map with non-vanishing derivative is itself
--   complex differentiable, with the reciprocal derivative. This is the Lean analogue of HOL
--   Light's `HOLOMORPHIC_ON_INVERSE`, which Mathlib does not currently provide. Continuity of the
--   inverse comes from the open mapping property, after which `HasDerivAt.of_local_left_inverse`
--   supplies the derivative.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L279-L313
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L279-L313

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
import Definitions.Def_ExpChaotic_Expansion
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.lemma3_hasDerivAt_invFunOn
    {g : ℂ → ℂ} {b : ℂ} {r : ℝ}
    (hg : DifferentiableOn ℂ g (ball b r))
    (hinj : Set.InjOn g (ball b r))
    (hne : ∀ z ∈ ball b r, deriv g z ≠ 0)
    {w : ℂ} (hw : w ∈ g '' ball b r) :
    HasDerivAt (Function.invFunOn g (ball b r))
      (deriv g (Function.invFunOn g (ball b r) w))⁻¹ w := by sorry
