-- Prove2me | Theorems.Thm_AFT_BinaryArithmetic_gcd_resources
-- name    : AFT.BinaryArithmetic.gcd_resources
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:17:54.79532+00:00
-- url     : https://prove2.me/theorems/9f340bcb-e87a-4508-baac-b7a3cb637ce3
-- title:
--   Length and cubic charge bounds for the binary gcd
-- statement:
--   For two supplied natural-number bit strings of lengths $a$ and $b$, the native Euclidean gcd computation returns a bit string of length at most $\max\{a,b\}$ and satisfies
--
--   $$\operatorname{len}(\operatorname{gcd})\le\max\{a,b\},\qquad W(\operatorname{gcd})\le1000(a+b+1)^3.$$
--
--   The bounds include normalization of redundant high zero bits in the inputs.
--
--   Here $W$ denotes the operation charge recorded by the native counted program. The bound is an accounting lemma for the constructive sampler, not a separate certificate in a Turing-machine model.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/BinaryEuclid.lean, lines 162–177; exact native theorem type and complete proof.

import Definitions.Def_InfoLossLAR_Native_AFT_BinaryEuclid
import Mathlib



/-! A binary implementation of Euclid with an explicit linear-in-bitlength
iteration bound. Each iteration performs two long divisions, which halves
the second nonzero operand. -/
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
section AFT
section BinaryArithmetic
open AFT
open AFT.BinaryArithmetic

theorem AFT.BinaryArithmetic.gcd_resources (as bs : List Bool) :
    (_root_.AFT.BinaryArithmetic.gcd as bs).digits.length ≤ max as.length bs.length ∧
      (_root_.AFT.BinaryArithmetic.gcd as bs).work ≤ 1000*(as.length+bs.length+1)^3 := by sorry
