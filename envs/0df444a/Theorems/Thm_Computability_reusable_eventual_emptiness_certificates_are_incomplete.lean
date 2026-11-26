-- Prove2me | Theorems.Thm_Computability_reusable_eventual_emptiness_certificates_are_incomplete
-- name    : Computability.reusable_eventual_emptiness_certificates_are_incomplete
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T18:45:33.597283+00:00
-- url     : https://prove2.me/theorems/dd06ec53-df4e-582d-9522-0c1ffba543eb
-- title:
--   Incompleteness of reusable eventual-emptiness certificates
-- statement:
--   Fix natural numbers a and b with b positive. For a partial recursive code c, call c eventually empty on the progression a + bi if the bounded evaluator at input 0 returns no result at every sufficiently late fuel value on that progression. Consider any computable checker that takes c and a natural number encoding a finite certificate. Suppose every certificate it accepts proves that c is eventually empty on the whole progression. Then there is an eventually empty code whose certificates the checker all rejects.
-- source:
--   A corollary of the non-enumerability of nonhalting. See Mario Carneiro, Formalizing Computability Theory via Partial Recursive Functions, ITP 2019, https://doi.org/10.4230/LIPIcs.ITP.2019.12.

import Mathlib.Computability.Halting

open Nat.Partrec (Code)

theorem Computability.reusable_eventual_emptiness_certificates_are_incomplete (offset period : ℕ)
    (positive : 0 < period) (check : Code × ℕ → Bool) (computable : Computable check)
    (sound : ∀ c z, check (c,z) = true → ∃ threshold, ∀ i ≥ threshold,
      (Nat.Partrec.Code.evaln (offset + period * i) c 0).isSome = false) :
    ∃ c, (∃ threshold, ∀ i ≥ threshold,
      (Nat.Partrec.Code.evaln (offset + period * i) c 0).isSome = false) ∧
      ∀ z, check (c,z) = false := by sorry
