-- Prove2me | Theorems.Thm_DerivativeChainPrivate_real_close_predecessor
-- name    : DerivativeChainPrivate.real_close_predecessor
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T03:08:26.086991+00:00
-- url     : https://prove2.me/theorems/b06c65a5-2c67-4cc2-aa78-af4a56f2057a
-- title:
--   Real unit-interval close predecessor
-- statement:
--   Let I be a finite type with decidable equality and s a nonempty finite subset. Let real weights p_i be nonnegative on s and sum to one. Let real points a_i lie in [-1,1] on s, and put b equal to their weighted mean. Then
--
--   $$\exists i\in s:\quad (a_i-b)^2\le 1-b^2.$$
--
--   The result is a one-step convex-combination estimate. It asserts no compatible chain through multiple derivative layers.
-- source:
--   Derivative-zero chains: public formalization reference, R10, DerivativeChainPrivate.real_close_predecessor. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem DerivativeChainPrivate.real_close_predecessor {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (p a : ι → ℝ) (b : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1)
    (hb : b = ∑ i ∈ s, p i * a i)
    (hmem : ∀ i ∈ s, |a i| ≤ 1) :
    ∃ i ∈ s, (a i - b) ^ 2 ≤ 1 - b ^ 2  := by sorry
