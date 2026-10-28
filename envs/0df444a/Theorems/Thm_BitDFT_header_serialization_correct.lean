-- Prove2me | Theorems.Thm_BitDFT_header_serialization_correct
-- name    : BitDFT.header_serialization_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:32:26.444488+00:00
-- url     : https://prove2.me/theorems/d316a2b5-9cbf-4750-ac2e-683735e6c4ad
-- title:
--   Serialize both headers with canonical precision in linear time
-- statement:
--   Let n be a retained binary dimension word, w a positive-valued little-endian precision word, and o an output prefix. One fixed five-tape machine appends the self-delimiting header of n followed by encNat(value(w)) within 2|n|+2|w|+2 size(value(w))+12 transitions. It preserves native input, retains the dimension word, clears the old precision tape, and retains the canonical precision bits on the destination tape. Its complete final configuration, including every head position, is specified. No free rearrangement or padding-removal step is assumed.
-- source:
--   Assembles accepted dimension serialization, exact canonicalization, tape routing, and finite-controller sequencing. This is the two-header serialization stage; copying the native suffix and constructing the full Fourier-machine wrapper remain separate obligations.

import Definitions.Def_BitDFT_HeaderSerialization
open BitDFT BitDFT.HeaderSerialization IntMul

theorem BitDFT.header_serialization_correct (base : storage.Cfg) (n w out : List Bool) (hw : 0 < BinaryCounter.value w) :
    ∃ t, t ≤ 2*n.length+2*w.length+2*(BinaryCounter.value w).size+12 ∧
      machine.step^[t] (initial base n w out) = final base n w out := by sorry
