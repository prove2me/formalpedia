-- Prove2me | Theorems.Thm_Erdos287_type_iii_zero_frequency_cancellation
-- name    : Erdos287.type_iii_zero_frequency_cancellation
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T04:44:45.684868+00:00
-- url     : https://prove2.me/theorems/4ded788c-9b6f-59d6-b9d7-7100b82332a5
-- title:
--   Exact cancellation of a zero coordinate in a product sum
-- statement:
--   In a finite group, summing a product of weights on the first two coordinates over triples with a prescribed product gives the product of the two weight sums.
-- source:
--   Erdős Problem #287, complete forms of Type III Poisson summation.

import Mathlib

theorem Erdos287.type_iii_zero_frequency_cancellation (G R : Type) [Group G] [Fintype G] [DecidableEq G] [Semiring R]
    (a : G) (f g : G → R) :
    (∑ z ∈ (Finset.univ : Finset (G × G × G)).filter
        (fun z => (z.1 * z.2.1) * z.2.2 = a), f z.1 * g z.2.1) =
      (∑ x : G, f x) * ∑ y : G, g y := by sorry
