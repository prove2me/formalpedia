-- Prove2me | solution 1 for prime_7_yukon_a064305e92ee
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T04:17:59.766472+00:00
-- url     : https://prove2.me/submissions/dd55cca8-8acc-410a-9347-f51a639fe45e

/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.LucasPrimality


public import Definitions.Def_Yukon_92052b9f6262f4f17145e198
public import Definitions.Def_Yukon_8b59f57debbd0f7955ae4947
public import Definitions.Def_Yukon_5a1c8f8f8be9100f7eedfb21
public import Definitions.Def_Yukon_20fdbb063a4c0f803b6a5b04
public import Definitions.Def_Yukon_adcae76b85f03179c58a98cf
@[expose] public section
/-!
# The Lucas test for primes.

This file implements the Lucas test for primes (not to be confused with the Lucas-Lehmer test for
Mersenne primes). A number `a` witnesses that `n` is prime if `a` has order `n-1` in the
multiplicative group of integers mod `n`. This is checked by verifying that `a^(n-1) = 1 (mod n)`
and `a^d ≠ 1 (mod n)` for any divisor `d | n - 1`. This test is the basis of the Pratt primality
certificate.

## TODO

- Bonus: Show the reverse implication i.e. if a number is prime then it has a Lucas witness.
  Use `Units.IsCyclic` from `RingTheory/IntegralDomain` to show the group is cyclic.
- Write a tactic that uses this theorem to generate Pratt primality certificates
- Integrate Pratt primality certificates into the norm_num primality verifier

## Implementation notes

Note that the proof for `lucas_primality` relies on analyzing the multiplicative group
modulo `p`. Despite this, the theorem still holds vacuously for `p = 0` and `p = 1`: In these
cases, we can take `q` to be any prime and see that `hd` does not hold, since `a^((p-1)/q)` reduces
to `1`.
-/

@[expose] public section

section New

-- TODO: port to `Mathlib`?
end New
-- cannot do ^1 correctly it seems?
theorem _root_.solution : Nat.Prime 7  := by
  refine PrattCertificate.out ⟨3, by reduce_mod_char, ?_⟩
  refine .split 2 3 ?_ ?_ (by norm_num)
  · exact .prime 2 1 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ prime_3 (by reduce_mod_char; decide) (by norm_num)
end
end
