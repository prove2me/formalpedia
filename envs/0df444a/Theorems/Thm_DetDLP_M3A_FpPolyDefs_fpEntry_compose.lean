-- Prove2me | Theorems.Thm_DetDLP_M3A_FpPolyDefs_fpEntry_compose
-- name    : DetDLP.M3A.FpPolyDefs.fpEntry_compose
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T00:29:26.281146+00:00
-- url     : https://prove2.me/theorems/67acb7ca-2501-4a95-96d5-f255c351567d
-- title:
--   DetDLP WireKit: M3A FpPolyDefs fpEntry compose
-- statement:
--   Compose size extractors with ordinary-gate and lookup PolyT certificates into total polynomial-time `fpEntry`.
-- source:
--   DetDLP WireKit deep-sketch private children (separator/polywire assemble)

import Definitions.Def_DetDLP_M3A_FpPolyDefs

set_option autoImplicit false

open DetDLP.M3A.FpPolyDefs Groundwork

/-- Compose size/field extractors with ordinary-gate and lookup evaluators into
    total polynomial-time `fpEntry`. -/

theorem DetDLP.M3A.FpPolyDefs.fpEntry_compose
    (hsup : PolyT d ∧ PolyT m ∧ PolyT k ∧ PolyT pre ∧ PolyT sizeField ∧ PolyT prec ∧ PolyT len)
    (hord : PolyT (fun z : List Bool × ℕ × List Bool =>
      indicator (len z.1) (ordinary z.1 z.2.1 z.2.2)))
    (hlu : PolyT (fun z : List Bool × ℕ × List Bool => lookup z.1 z.2.1 z.2.2)) :
    PolyT fpEntry := by sorry
