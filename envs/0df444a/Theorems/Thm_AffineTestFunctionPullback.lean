-- Prove2me | Theorems.Thm_AffineTestFunctionPullback
-- name    : AffineTestFunctionPullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:09:46.242546+00:00
-- url     : https://prove2.me/theorems/b5115595-5417-4075-a03a-6682a938025b
-- title:
--   Affine Test Function Pullback: Affine Test Function Pullback
-- statement:
--   THE TEST-FUNCTION CORRESPONDENCE UNDER AN AFFINE SUBSTITUTION.  Write `T x = x₀ + r • x` for
--   the affine dilation and `S y = r⁻¹ • (y - x₀)` for its inverse, `r > 0`.  If `φ` is a test
--   function admissible for the PULLED-BACK domain `T⁻¹ Ω = {x | x₀ + r • x ∈ Ω}` -- smooth, compactly
--   supported, with `tsupport φ` inside that set -- then its pushforward `ψ := φ ∘ S` is a test
--   function admissible for `Ω` itself, and the two gradients are related by the chain rule
--
--   `gradient φ x = r • gradient ψ (x₀ + r • x)`   for every `x`.
--
--   Four conclusions, because a test function is four things at once: smoothness, compact support,
--   support inside the domain, and -- for a weak formulation -- a known gradient.  All four are
--   needed together, which is why they are one lemma: a weak equation on the rescaled domain is
--   tested against `φ` and must be matched against the original equation tested against `ψ`, so
--   every clause is consumed at the same moment.
--
--   The support clause is where the substitution does real work.  `tsupport ψ` is contained in
--   `S⁻¹(tsupport φ)`, which equals the IMAGE `T(tsupport φ)` because `T` and `S` are mutually
--   inverse; compactness then transfers along the continuous `T`, and membership in `Ω` follows from
--   `tsupport φ ⊆ T⁻¹ Ω` after cancelling `T ∘ S`.  The factor `r` in the gradient clause, rather
--   than `r⁻¹`, is likewise forced: `DS = r⁻¹ I`, so the chain rule puts `r⁻¹` on the pushforward's
--   gradient and `r` appears when that is solved for the original.
--
--   No hypothesis on `Ω` is needed -- not even openness.  The statement is about supports and the
--   chain rule, both of which are insensitive to it.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/AffineTestFunctionPullback.lean#L26-L87
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/AffineTestFunctionPullback.lean#L26-L87

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_AffineTestFunctionPullback
set_option autoImplicit false

theorem AffineTestFunctionPullback (x₀ : Plane) (r : ℝ) (hr : 0 < r) (Ω : Set Plane) :
    ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ {x : Plane | x₀ + r • x ∈ Ω} →
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Plane => φ (r⁻¹ • (y - x₀)))
      ∧ HasCompactSupport (fun y : Plane => φ (r⁻¹ • (y - x₀)))
      ∧ tsupport (fun y : Plane => φ (r⁻¹ • (y - x₀))) ⊆ Ω
      ∧ (∀ x : Plane, gradient φ x
          = r • gradient (fun y : Plane => φ (r⁻¹ • (y - x₀))) (x₀ + r • x)) := by sorry
