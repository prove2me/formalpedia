-- Prove2me | Theorems.Thm_BitDFT_tape_permutation_run
-- name    : BitDFT.tape_permutation_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:14:46.273803+00:00
-- url     : https://prove2.me/theorems/1c86cb27-f0f6-4aca-bb20-d7626c85fae8
-- title:
--   Finite tape relabeling preserves complete runs at the identical clock
-- statement:
--   For every multitape machine, every finite permutation of its tapes fixing the input tape, every configuration, and every transition count t, the relabeled machine after t transitions is exactly the relabeling of the original machine after t transitions. The equality includes state, every tape cell, and every head position. No runtime overhead or initialization assumption is required; the output tape follows the chosen permutation unless it too is fixed.
-- source:
--   The finite transition table routes each read and write through inverse tape permutations. A one-step commuting equality and induction yield the complete run equality. Used to park precision data while the logarithmic scanner uses a different work tape.

import Definitions.Def_BitDFT_TapePermutation
open BitDFT.TapePermutation IntMul

theorem BitDFT.tape_permutation_run (M : MultitapeTM) (e : Fin M.k ≃ Fin M.k) (he : e M.inTape = M.inTape)
    (c : M.Cfg) (t : ℕ) :
    (machine M e he).step^[t] (embed M e he c) = embed M e he (M.step^[t] c) := by sorry
