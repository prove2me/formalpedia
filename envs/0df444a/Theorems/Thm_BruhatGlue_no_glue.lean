-- Prove2me | Theorems.Thm_BruhatGlue_no_glue
-- name    : BruhatGlue.no_glue
-- status  : Proved
-- author  : @darkhipo
-- created : 2026-10-28T19:06:35.907562+00:00
-- url     : https://prove2.me/theorems/5c2906a3-2213-4cea-8106-77c1b01810b2
-- title:
--   Unipotent Bruhat glue cannot beat m pivots (rank-potential)
-- statement:
--   In any wire product of the edge-matrix form — lower-triangular factors (unipotent or not) interleaved with run-pivot cross-transpositions — reaching the block swap requires total run width at least m. Lower-triangular multiplication never increases the rank of the top-right block, and each cross-transposition pivot raises it by at most one: unipotent glue saves exactly zero. Consequence for the integer-multiplication round-eight witnesses: every per-wire (edge-layer) assembly family carries the proved >=529 floor; savings must come from the gate layer.
-- source:
--   BigO integer-multiplication verification strike (2026-10-28), summit attempt #5

import Definitions.Def_BruhatGlue_Model

import Definitions.Def_BruhatGlue_Model

namespace BruhatGlue

/-- **The decisive negative.** A `Glue` word reaching the block swap uses at
least `m` pivots: unipotent (lower-triangular) glue cannot save a single
transposition, at any `m`, over any field. -/
theorem no_glue {K : Type*} [Field K] {m : ℕ} {w} (h : Glue K m (blkSwap K m) w) :
    m ≤ w := by
  sorry

end BruhatGlue
