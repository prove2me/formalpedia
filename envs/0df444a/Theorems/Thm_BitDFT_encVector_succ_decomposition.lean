-- Prove2me | Theorems.Thm_BitDFT_encVector_succ_decomposition
-- name    : BitDFT.encVector_succ_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T00:48:33.319305+00:00
-- url     : https://prove2.me/theorems/2136a204-e7c3-4a11-b5e1-796c173674c9
-- title:
--   A fixed-width vector encoding splits at its first coordinate
-- statement:
--   For every fixed field width and every nonempty vector of complex integer coordinates, the encoded vector is the encoded first coordinate followed by the same encoding of the remaining coordinates. In symbols, for $U : \mathrm{Fin}(n+1) \to \mathbb{Z} \times \mathbb{Z}$,
--
--   $$\operatorname{encVector}_w(U)=\operatorname{encComplex}_w(U(0))\,\Vert\,\operatorname{encVector}_w(i\mapsto U(i+1)).$$
--
--   This exact decomposition supplies the suffix invariant for a coordinate-by-coordinate output pass.
-- source:
--   A structural vector-record invariant used to build and verify the repeated coordinate pass in BitDFT.rescale_output_machine.

import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.List.OfFn
set_option autoImplicit false
open BitDFT IntMul

theorem BitDFT.encVector_succ_decomposition {n : ℕ} (w : ℕ) (U : Fin (n + 1) → ℤ × ℤ) :
    encVector w U = encComplex w (U 0) ++
      encVector w (fun i : Fin n => U i.succ) := by sorry
