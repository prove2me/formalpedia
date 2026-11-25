-- Prove2me | Theorems.Thm_DetDLP_M3A_FpPolyDefs_entry_support
-- name    : DetDLP.M3A.FpPolyDefs.entry_support
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T23:36:10.748425+00:00
-- url     : https://prove2.me/theorems/5361140a-bd6d-4779-93fa-0824fd94b4ce
-- title:
--   Uniform polynomial bounds for native finite-field entry parameters
-- statement:
--   The decoded dimensions, prefix length, field-size budget, precision, and output length used by the native finite-field entry evaluator are uniformly polynomial-time computable from the input word.
-- source:
--   DetDLP, Section 4, native finite-field wire programs.

import Definitions.Def_DetDLP_M3A_FpPolyDefs
open Groundwork

theorem DetDLP.M3A.FpPolyDefs.entry_support {α : Type} [Enc α] : PolyT DetDLP.M3A.FpPolyDefs.d ∧ PolyT DetDLP.M3A.FpPolyDefs.m ∧ PolyT DetDLP.M3A.FpPolyDefs.k ∧ PolyT DetDLP.M3A.FpPolyDefs.pre ∧ PolyT DetDLP.M3A.FpPolyDefs.sizeField ∧ PolyT DetDLP.M3A.FpPolyDefs.prec ∧ PolyT DetDLP.M3A.FpPolyDefs.len := by sorry
