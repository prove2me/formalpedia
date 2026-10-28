-- Prove2me | Theorems.Thm_D1Bound5_bennett_two_taylor_scalar_mem
-- name    : D1Bound5.bennett_two_taylor_scalar_mem
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:49.198608+00:00
-- url     : https://prove2.me/theorems/0f02ed35-d722-4b15-91d8-44294cdd32e9
-- title:
--   Bennett two taylor scalar mem
-- statement:
--   The three binomial factors in the two-node Taylor expansion are integral after the uniform order-k power of four is included. Every integer is in S.
-- source:
--   D1Bound5/BennettSubringSums.lean, lines 27-38, SHA-256 5c21c49f96a2c66d645b20532b67dda8cde35833f4e0f3fe6b545b7454d81ecf. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

section
open Finset

namespace D1Bound5




theorem _root_.D1Bound5.bennett_two_taylor_scalar_mem
    {F : Type*} [Field F] [CharZero F] (S : Subring F)
    (k h p q u v : ℕ) (hh : h ≤ k) :
    (((4 : F) ^ k * Ring.choose ((k : F) + 1 / 2) h) *
      Ring.choose (-(p : F)) u * Ring.choose (-(q : F)) v) ∈ S := by sorry

end D1Bound5
end
