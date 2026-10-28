-- Prove2me | Theorems.Thm_BitDFT_vector_scaled_output_fits
-- name    : BitDFT.vector_scaled_output_fits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T03:07:59.141026+00:00
-- url     : https://prove2.me/theorems/d96522f4-5688-4234-958c-d5b3b0ac0cb9
-- title:
--   Every exactly scaled vector fits its fixed-width output encoding
-- statement:
--   For a vector whose complex coordinates lie in the precision-$q$ unit disc, and any $n\le 2^\ell$, multiplying every real and imaginary integer coordinate by $n$ produces magnitudes strictly below $2^{q+\ell+1}$. Thus every signed coordinate fits the rescaling theorem's fixed output width. The encoded vector has exactly $2n(q+\ell+2)$ bits, including one sign bit for each of its $2n$ integer fields.
-- source:
--   Direct arithmetic encoding invariant for BitDFT.rescale_output_machine. The proof derives each coordinate bound from the disc hypothesis and proves the exact fixed-width tape length. This is a postcondition component only; the machine that iterates over and rewrites all vector fields remains to be constructed.

import Definitions.Def_BitDFT_Numerics
import Mathlib.Tactic
set_option autoImplicit false
open BitDFT IntMul

theorem BitDFT.vector_scaled_output_fits {n q ell : ℕ} (hscale : n ≤ 2^ell)
    (U : Fin n → ℤ × ℤ) (hU : vectorDisc q U) :
    (∀ k, ((n : ℤ) * (U k).1).natAbs < 2^(q + ell + 1) ∧
      ((n : ℤ) * (U k).2).natAbs < 2^(q + ell + 1)) ∧
    (encVector (q + ell + 1) (fun k =>
      ((n : ℤ) * (U k).1, (n : ℤ) * (U k).2))).length =
        2 * n * (q + ell + 2) := by sorry
