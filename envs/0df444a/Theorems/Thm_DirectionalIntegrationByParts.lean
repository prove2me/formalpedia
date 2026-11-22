-- Prove2me | Theorems.Thm_DirectionalIntegrationByParts
-- name    : DirectionalIntegrationByParts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:21.736557+00:00
-- url     : https://prove2.me/theorems/fa91c251-7156-4066-89fe-7927403ace02
-- title:
--   Directional Integration By Parts: Directional Integration By Parts
-- statement:
--   Integration by parts in a fixed direction, for the inner product of two vector fields:
--   if `X` is `C^1` on an open `U` and `Y` is `C^1` on the plane with compact support inside `U`,
--   then for every direction `e`
--   `∫_U ⟪D X(x)[e], Y x⟫ = - ∫_U ⟪X x, D Y(x)[e]⟫`.
--
--   This is the step that moves a directional derivative off one factor and onto the other inside a
--   weak formulation.  Its consumer differentiates the `p`-harmonic equation: there `X` is the flux
--   `A_p ∘ Dv` and `Y` is the gradient of a test function, and this lemma is what turns a
--   directional derivative of the test function into one of the flux.
--
--   Only `C^1` is assumed of `X`, and only on `U`; the compact support of `Y` inside `U` is what
--   makes the pairing `⟪X, Y⟫` globally `C^1` even though `X` is controlled only on `U`, since `U`
--   and the complement of `tsupport Y` are two open sets covering the plane on the second of which
--   the pairing vanishes identically.  That is also why the hypothesis is `tsupport Y ⊆ U` rather
--   than `Function.support Y ⊆ U`.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/DirectionalIntegrationByParts.lean#L18-L144
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/DirectionalIntegrationByParts.lean#L18-L144

import Definitions.Def_PHigherOrder_TestFunctionGradientIntegral
import Definitions.Def_PHigherOrder_DirectionalIntegrationByParts
import Theorems.Thm_TestFunctionGradientIntegral

set_option autoImplicit false

theorem DirectionalIntegrationByParts (U : Set Plane) (hU : IsOpen U)
    (X : Plane → Plane) (hX : ContDiffOn ℝ 1 X U)
    (Y : Plane → Plane) (hY : ContDiff ℝ 1 Y) (hYsupp : HasCompactSupport Y)
    (hYU : tsupport Y ⊆ U) (e : Plane) :
    ∫ x in U, inner ℝ (fderiv ℝ X x e) (Y x)
      = - ∫ x in U, inner ℝ (X x) (fderiv ℝ Y x e) := by sorry
