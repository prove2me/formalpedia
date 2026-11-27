-- Prove2me | Theorems.Thm_CumulativeBlockCode_capacity_and_fidelity
-- name    : CumulativeBlockCode.capacity_and_fidelity
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T22:31:40.488091+00:00
-- url     : https://prove2.me/theorems/238c3a39-ddac-4279-85dd-51cb25ee790c
-- title:
--   Two padded streams faithfully encode block lists at a cumulative budget
-- statement:
--   Let H and E be the sizes of the finite header and cell alphabets. The code for at most r blocks and at most s cells in total has (H+1)^r (E+2)^(r+s) possible values. Equal codes recover the exact block lists under those bounds, including empty blocks.
-- source:
--   Finite encodings for sparse crossing-sequence arguments.

import Definitions.Def_CumulativeCrossingBlocks

open CumulativeBlockCode

theorem CumulativeBlockCode.capacity_and_fidelity {Header Cell : Type} [Fintype Header] [Fintype Cell] (blocks cells : ℕ) :
    Fintype.card (Code Header Cell blocks cells) =
      (Fintype.card Header+1)^blocks * (Fintype.card Cell+2)^(blocks+cells) ∧
    (∀ (x y : List (Header × List Cell)),
      x.length ≤ blocks → totalCells x ≤ cells → y.length ≤ blocks → totalCells y ≤ cells →
      encode blocks cells x = encode blocks cells y → x = y) := by sorry
