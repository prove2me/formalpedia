-- Prove2me | Theorems.Thm_BitDFT_bval_foldField_false
-- name    : BitDFT.bval_foldField_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T04:36:25.147628+00:00
-- url     : https://prove2.me/theorems/93773984-0d04-4317-83a5-3b1f9cfb50bc
-- title:
--   The digit fold is a carry-propagating addition
-- statement:
--   Let $l$ be a field of bits read least significant first, with value $v$, and let $\kappa \in \{0,1\}$ be an incoming carry. Folding the field with the two's-complement carry switched off — the machine's per-bit rule with $g = 0$ — pushes the bits of $v + \kappa$ and reports as its carry out the overflow past the field:
--   $$\operatorname{bval}\bigl(\text{pushed bits}\bigr) + \text{carry out}\cdot 2^{|l|} = v + \kappa .$$
--
--   So the field's digit is obtained from the field's value by one carry-propagating addition, and the carry out is exactly what the next field has to absorb. This is the arithmetic content of the unpacking machine's inner loop: it is what makes the balanced base-$2^\beta$ digit of a field depend only on that field's value and on the carry arriving from the field to its right.
-- source:
--   Internal: the inner-loop arithmetic of the Prove2me theorem BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98), against the machine definition BitDFT_unpackerMachine and the arithmetic kernel of IntMul.HvdH.kunpack.

import Definitions.Def_BitDFT_foldField

theorem BitDFT.bval_foldField_false (κ : Bool) (l : List Bool) :
    bval (foldField false κ l).1
        + (foldField false κ l).2.2.1.toNat * 2 ^ l.length = bval l + κ.toNat := by sorry
