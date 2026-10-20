-- Prove2me | Theorems.Thm_DerivativeChainPrivate_complex_close_predecessor
-- name    : DerivativeChainPrivate.complex_close_predecessor
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T03:08:26.574276+00:00
-- url     : https://prove2.me/theorems/a412b3c1-a643-49c1-921f-ddb15df8e7f8
-- title:
--   Complex unit-disk close predecessor
-- statement:
--   Let I be a finite type with decidable equality and s a nonempty finite subset. Let real weights p_i be nonnegative on s and sum to one. Let complex points a_i have norm at most one on s. Suppose the real and imaginary components of b equal the corresponding weighted component sums. Then
--
--   $$\exists i\in s:\quad |a_i-b|^2\le 1-|b|^2.$$
--
--   Only one predecessor step is asserted. No derivative-root representation or multistep bound is assumed or concluded.
-- source:
--   Derivative-zero chains: public formalization reference, R11, DerivativeChainPrivate.complex_close_predecessor. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem DerivativeChainPrivate.complex_close_predecessor {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (p : ι → ℝ) (a : ι → ℂ) (b : ℂ)
    (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1)
    (hbre : b.re = ∑ i ∈ s, p i * (a i).re)
    (hbim : b.im = ∑ i ∈ s, p i * (a i).im)
    (hmem : ∀ i ∈ s, ‖a i‖ ≤ 1) :
    ∃ i ∈ s, ‖a i - b‖ ^ 2 ≤ 1 - ‖b‖ ^ 2  := by sorry
