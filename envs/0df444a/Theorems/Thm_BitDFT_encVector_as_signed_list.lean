-- Prove2me | Theorems.Thm_BitDFT_encVector_as_signed_list
-- name    : BitDFT.encVector_as_signed_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T02:27:40.716221+00:00
-- url     : https://prove2.me/theorems/bfa67b08-0f15-41d2-9770-8e8ae8e84bf0
-- title:
--   Read a complex vector as one flattened signed list
-- statement:
--   For every fixed-width complex vector encoding, flatten each coordinate into its real component followed by its imaginary component. The resulting tape is exactly the ordinary fixed-width signed-integer list encoding of that flattened sequence, whose length is twice the vector dimension. Thus the packed scaling stage can consume the existing vector tape directly as a signed list.
-- source:
--   Exact encoding identity for the packed multiplier wrapper used in BitDFT.rescale_output_machine.

import Definitions.Def_BitDFT_Encoding
set_option autoImplicit false
open BitDFT

theorem BitDFT.encVector_as_signed_list {n : ℕ} (w : ℕ) (U : Fin n → ℤ × ℤ) :
    encVector w U = encList w
      ((List.finRange n).flatMap (fun i : Fin n => [(U i).1, (U i).2])) ∧
    ((List.finRange n).flatMap (fun i : Fin n => [(U i).1, (U i).2])).length = 2*n := by sorry
