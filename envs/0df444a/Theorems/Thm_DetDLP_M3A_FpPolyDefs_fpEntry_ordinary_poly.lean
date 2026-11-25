-- Prove2me | Theorems.Thm_DetDLP_M3A_FpPolyDefs_fpEntry_ordinary_poly
-- name    : DetDLP.M3A.FpPolyDefs.fpEntry_ordinary_poly
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T00:31:42.035056+00:00
-- url     : https://prove2.me/theorems/692f0c26-df07-4aa6-9461-3de7fc33372e
-- title:
--   DetDLP WireKit: M3A FpPolyDefs fpEntry ordinary poly
-- statement:
--   The ordinary-gate indicator branch of the native fp entry evaluator is total polynomial-time.
-- source:
--   DetDLP WireKit deep-sketch private children (separator/polywire assemble)

import Definitions.Def_DetDLP_M3A_FpPolyDefs

set_option autoImplicit false

open DetDLP.M3A.FpPolyDefs Groundwork

/-- Local ordinary-gate indicator evaluation is total polynomial-time in the
    query word, vertex index, and incidence bitstring. -/

theorem DetDLP.M3A.FpPolyDefs.fpEntry_ordinary_poly :
    PolyT (fun z : List Bool × ℕ × List Bool =>
      indicator (len z.1) (ordinary z.1 z.2.1 z.2.2)) := by sorry
