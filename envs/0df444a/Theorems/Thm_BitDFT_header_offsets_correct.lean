-- Prove2me | Theorems.Thm_BitDFT_header_offsets_correct
-- name    : BitDFT.header_offsets_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:55:29.267909+00:00
-- url     : https://prove2.me/theorems/66404c2d-600f-46bd-a9c0-0f2fc54d567b
-- title:
--   Exact header parsing after an arbitrary input prefix
-- statement:
--   For arbitrary bit strings pre, v, and rest, the fixed stopped reader parses the header consisting of |v| unary ones, a zero, and v after pre. Starting with its input head at |pre|, it reaches the specified full final configuration in exactly 2|v|+3 steps. The retained field is v, the counter is blank, the native input is preserved, and all final head positions are specified.
-- source:
--   A supporting component for parsing the dimension and requested precision in the integer-multiplication-to-DFT machine construction. This theorem alone does not close either main open machine theorem.

import Definitions.Def_BitDFT_HeaderOffsets
open BitDFT BitDFT.HeaderOffsets IntMul

theorem BitDFT.header_offsets_correct (pre v rest : List Bool) :
    let x := pre ++ List.replicate v.length true ++ false :: (v ++ rest)
    HeaderReader.stage.machine.step^[2*v.length+3] (prepared x pre.length) =
      finished x pre.length v := by sorry
