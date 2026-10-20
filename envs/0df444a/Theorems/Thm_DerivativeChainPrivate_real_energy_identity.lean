-- Prove2me | Theorems.Thm_DerivativeChainPrivate_real_energy_identity
-- name    : DerivativeChainPrivate.real_energy_identity
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T03:08:25.424415+00:00
-- url     : https://prove2.me/theorems/bd4ee54d-6636-45da-b3b8-c71a0dea77cf
-- title:
--   Real weighted energy identity
-- statement:
--   Let I be a finite type with decidable equality, s a finite subset, p and a real-valued functions on I, and b real. If the weights on s sum to one and b is their weighted sum of the a-values, then
--
--   $$\sum_{i\in s}p_i(a_i-b)^2=\sum_{i\in s}p_i a_i^2-b^2.$$
--
--   No positivity assumption on the weights is needed. This is an algebraic identity, not a derivative-chain bound.
-- source:
--   Derivative-zero chains: public formalization reference, R09, DerivativeChainPrivate.real_energy_identity. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem DerivativeChainPrivate.real_energy_identity {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (p a : ι → ℝ) (b : ℝ)
    (hsum : ∑ i ∈ s, p i = 1)
    (hb : b = ∑ i ∈ s, p i * a i) :
    ∑ i ∈ s, p i * (a i - b) ^ 2 = ∑ i ∈ s, p i * (a i) ^ 2 - b ^ 2  := by sorry
