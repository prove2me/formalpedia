-- Prove2me | Theorems.Thm_BitDFT_output_length_le_time
-- name    : BitDFT.output_length_le_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:37:33.774657+00:00
-- url     : https://prove2.me/theorems/32b8b632-fa91-4c36-aefc-c919a87a4acc
-- title:
--   An actual output tape cannot contain more bits than elapsed steps
-- statement:
--   Let $M$ be a deterministic multitape machine with the mission's blank initial output tape. If it halts on binary inputs $x,y$ after $t$ actual transitions with the complete output word $w$, then
--   $$|w|\le t.$$
--   The bound counts explicit output bits, including leading zeros. It follows from the unit-speed motion of the output head and does not assume a particular algorithm.
-- source:
--   Elementary output-size lower bound for the published IntMul.MultitapeTM model; unit head movement and blank initial output conventions in Definitions.Def_IntMul_MultitapeModel (Montanaro, Computational Complexity notes, §3).

import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.List.GetD
import Mathlib.Tactic.NormNum
set_option autoImplicit false
open IntMul

theorem BitDFT.output_length_le_time (M : MultitapeTM) (x y w : List Bool) (t : ℕ)
    (h : M.HaltsWithOutput x y t w) : w.length ≤ t := by sorry
