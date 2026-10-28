-- Prove2me | Theorems.Thm_BitDFT_encVector_prefix_decomposition
-- name    : BitDFT.encVector_prefix_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T00:57:16.437594+00:00
-- url     : https://prove2.me/theorems/263c5cec-4eb4-41ab-bb25-8179c0224772
-- title:
--   Every coordinate cursor splits an encoded vector into prefix and suffix
-- statement:
--   Fix a vector of $n$ complex integer coordinates and a fixed signed-field width $w$. At every cursor position $j$, its flat encoding splits exactly into the records indexed before $j$ followed by the records indexed from $j$ onward:
--
--   $$\operatorname{encVector}_w(U)=\Bigl(\mathop{\Vert}_{i\in\operatorname{take}(j,\mathrm{Fin}(n))}\operatorname{encComplex}_w(U(i))\Bigr)\,\Vert\,\Bigl(\mathop{\Vert}_{i\in\operatorname{drop}(j,\mathrm{Fin}(n))}\operatorname{encComplex}_w(U(i))\Bigr).$$
--
--   This identifies the exact unread suffix for a repeated coordinate-scanning machine.
-- source:
--   The all-cursor suffix invariant for the output-scaling pass in BitDFT.rescale_output_machine.

import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.List.OfFn
set_option autoImplicit false
open BitDFT IntMul

theorem BitDFT.encVector_prefix_decomposition {n : ℕ} (w j : ℕ) (U : Fin n → ℤ × ℤ) :
    encVector w U =
      ((List.finRange n).take j).flatMap (fun i => encComplex w (U i)) ++
      ((List.finRange n).drop j).flatMap (fun i => encComplex w (U i)) := by sorry
