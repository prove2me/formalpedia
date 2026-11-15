-- Prove2me | solution 2 for twin_prime_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-15T00:52:41.756598+00:00
-- url     : https://prove2.me/submissions/ae8d1775-fdca-4ce7-85b4-0a3fd5f0789c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_a166944_record_core
import Theorems.Thm_twin_prime_conjecture_of_target
import Theorems.Thm_A166944Research_a166944_record_is_greater_twin_prime

/-!
Reduction of the Twin Prime Conjecture to the A166944 difference-record statement.

The parent is the Twin Prime Conjecture in the form the mission states it: the set
of primes `p` with `p + 2` also prime is infinite, with no arguments.

Two children compose to give it:

  * `a166944_record_is_greater_twin_prime` -- every difference record of the OEIS
    A166944 recursion above 5 is the greater member of a twin-prime pair. This is
    `A166944Research.Target` written out, so it *is* the hypothesis the second child
    consumes.
  * `twin_prime_conjecture_of_target` -- that statement implies the Twin Prime
    Conjecture, proved by the project from the unboundedness of the record set.

So the whole remaining content of the Twin Prime Conjecture along this route is the
A166944 record statement. That statement is itself reduced further on the platform:
its frontier is the single inequality `2 * (sf - (M + 2)) <= M` for the canonical
capped replay, published as `a166944_travel_bound_from_45895573`.

Note the direction: this file does not assume the conjecture. It shows that the
conjecture follows from children that are themselves Open.

## Why this route is of a different kind

Every other reduction of the Twin Prime Conjecture on the platform takes an
analytic input: the first Hardy-Littlewood conjecture, Schinzel's Hypothesis H,
the Bateman-Horn conjecture, or the prime k-tuple conjecture. This one takes a
statement about a *computable recurrence*: the differences of
`a (n + 2) = a (n + 1) + gcd (...)` and their running maxima. The input is finitely
checkable in every range, and the project has verified it by kernel evaluation
through record 11751795063.

The reduction is not a weakening. `A166944Research.Target` implies the Twin Prime
Conjecture and is not implied by it: the conjecture says nothing about the record
set of a particular recursion. So the input is a *stronger* statement about a
*different object*, not a specialisation of a more general prime-gap conjecture as
the Polignac route is.
-/

open A166944Research

/-- The record statement, in the exact shape `Target` unfolds to. -/
theorem target_of_record_child :
    A166944Research.Target :=
  fun R hR hrec => a166944_record_is_greater_twin_prime R hR hrec

theorem solution :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite :=
  twin_prime_conjecture_of_target target_of_record_child
