-- Prove2me | solution 1 for levy_foundations_prodIteConstCard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:05:09.316801+00:00
-- url     : https://prove2.me/submissions/3203a2d6-ff16-4d9a-b470-f3a864397887

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Complex.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset

theorem solution
    {ι : Type*} (s : Finset ι) (p : ι → Prop)
    [DecidablePred p] (z : ℂ) :
    ∏ i ∈ s, (if p i then z else 1) = z ^ (s.filter p).card := by
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
