-- Prove2me | Theorems.Thm_AverageSensitivity_finite_coupling_refined
-- name    : AverageSensitivity.finite_coupling_refined
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-16T12:51:37.170628+00:00
-- url     : https://prove2.me/theorems/d868ab6f-94bc-4ede-a132-0fda2ff6ba88
-- title:
--   Refined one-sided coupling: mean squared displacement at most 4 a b + a squared
-- statement:
--   Let a finite set carry nonnegative probability weights w, and let U and V be two real-valued functions with identical weighted distributions. Let m be any real centre and a>=0. Assume V-U<=a at every point of positive weight. With b=E|U-m|, the conclusion is
--   $$\mathbb E (U-V)^2\le 4ab+a^2.$$
--   The distribution hypothesis means equality of E(phi(U)) and E(phi(V)) for every real function phi. The centre need not be the mean. This is the finite form of Lemma 2 of Lagdive, Aglave and Damre (2026), and is the probability refinement used by the coefficient-3.762 result.
-- source:
--   https://github.com/Anchen0823/average-sensitivity-lean/blob/b2e634415548e050c115f6f12732d8b6b4a5d27f/AverageSensitivity/RefinedCoupling.lean

import Mathlib
open scoped BigOperators

theorem AverageSensitivity.finite_coupling_refined {Ω : Type*} [Fintype Ω]
    (w U V : Ω → ℝ) (m a : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hsame : ∀ φ : ℝ → ℝ, ∑ i, w i * φ (U i) = ∑ i, w i * φ (V i))
    (ha : 0 ≤ a) (hstep : ∀ i, w i ≠ 0 → V i-U i ≤ a) :
    ∑ i, w i*(U i-V i)^2 ≤ 4*a*(∑ i, w i*|U i-m|)+a^2 := by sorry
