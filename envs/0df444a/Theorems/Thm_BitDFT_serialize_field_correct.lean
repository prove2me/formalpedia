-- Prove2me | Theorems.Thm_BitDFT_serialize_field_correct
-- name    : BitDFT.serialize_field_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:21:16.903059+00:00
-- url     : https://prove2.me/theorems/a96b6719-f57d-4de0-bd32-9517ee62217d
-- title:
--   Exact linear-time serialization of a retained binary field
-- statement:
--   For arbitrary binary field v and existing output prefix o, the fixed serializer appends exactly 1^{|v|}0v in 2|v|+3 transitions. The full final configuration retains v on tape 4, positions that head immediately after v, and positions the output head immediately after the appended header. All other tapes and heads are preserved. The result includes empty fields and arbitrary existing output prefixes.
-- source:
--   Full-configuration correctness and exact runtime for the actual finite serializer. Together with the precision stage it supports constructing the Fourier machine request, without treating encoding or head positioning as a free operation.

import Definitions.Def_BitDFT_SerializeField
open BitDFT.SerializeField IntMul

theorem BitDFT.serialize_field_correct (base : machine.Cfg) (v out : List Bool) :
    machine.step^[2*v.length+3] (frame base .start v out (v.length+1)) =
      frame base .halt v (out++List.replicate v.length true++false::v) (v.length+1) := by sorry
