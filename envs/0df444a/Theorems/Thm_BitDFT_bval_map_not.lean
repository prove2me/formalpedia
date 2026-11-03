-- Prove2me | Theorems.Thm_BitDFT_bval_map_not
-- name    : BitDFT.bval_map_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T02:13:39.507462+00:00
-- url     : https://prove2.me/theorems/144d264d-d71a-4909-a4da-8093879d8a14
-- title:
--   Complementing a bit list complements its value
-- statement:
--   Read a bit list least significant first and let $v$ be the number it denotes, with $m$ its length. Flipping every bit gives the number $2^m - 1 - v$: the complement of a bit string is the complement of its value within the range $[0, 2^m)$.
--
--   This is the first half of the two's-complement rule. A machine that reads the magnitude of a negative integer, walking from its least significant end, carries a single "still borrowing" bit: while that bit is set it flips the incoming bits and stops flipping at the first $1$. The statement here is what makes that rule correct, and it is used together with the addition-by-one half to turn the stored magnitude into the two's-complement residue the digit extraction works on.
-- source:
--   Internal: two's-complement bit rule for the machine proof of the Prove2me theorem BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98).

import Definitions.Def_BitDFT_bval

theorem BitDFT.bval_map_not (l : List Bool) :
    BitDFT.bval (l.map (fun b => !b)) = 2 ^ l.length - 1 - BitDFT.bval l := by sorry
