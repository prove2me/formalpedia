-- Prove2me | Theorems.Thm_AFT_BinaryArithmetic_RationalBits_ceilNatural_work
-- name    : AFT.BinaryArithmetic.RationalBits.ceilNatural_work
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:21:25.810168+00:00
-- url     : https://prove2.me/theorems/bf368bcd-ee13-42da-b0c4-58de992da0f4
-- title:
--   Quadratic charge for the natural ceiling
-- statement:
--   Let a signed rational encoding have numerator and denominator bit strings of lengths $a$ and $b$. Its natural-ceiling procedure satisfies
--
--   $$W(\operatorname{ceil}_{\mathbb N}(x))\le100(a+b+1)^2.$$
--
--   The statement applies to every valid canonical rational encoding.
--
--   Here $W$ denotes the operation charge recorded by the native counted program. The bound is an accounting lemma for the constructive sampler, not a separate certificate in a Turing-machine model.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/BinaryRationalControl.lean, lines 119–138; exact native theorem type and complete proof.

import Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalControl
import Mathlib


/-! # Actual binary clipping and natural ceiling

The ceiling uses binary long division, high-zero trimming, and one ripple
increment when the remainder is nonzero. Tests inspect the stored sign or
list constructor, never the decoded rational value.
-/
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
section AFT
section BinaryArithmetic
open AFT
open AFT.BinaryArithmetic
namespace AFT.BinaryArithmetic.RationalBits
end AFT.BinaryArithmetic.RationalBits
section RationalBits
open AFT
open AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits

theorem AFT.BinaryArithmetic.RationalBits.ceilNatural_work (input : RationalBits) :
    (ceilNatural input).work≤ 100*(input.numerator.length+input.denominator.length+1)^2 := by sorry
