-- Prove2me | Theorems.Thm_DetDLP_w3_fp_polywire_query_witness
-- name    : DetDLP.w3_fp_polywire_query_witness
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-25T00:30:58.666048+00:00
-- url     : https://prove2.me/theorems/866161f7-b4e5-48e0-9097-227e1ae4e455
-- title:
--   DetDLP WireKit: w3 fp polywire query witness
-- statement:
--   From the native finite-field wire-core family, produce for each fp query a concrete `WireCore` whose `fpBuild`/`fpEntry` packets realize the `w3_polyWireFamily` obligations at some fixed polynomial degree budget.
-- source:
--   DetDLP WireKit deep-sketch private children (separator/polywire assemble)

import Definitions.Def_DetDLP_W3_WireCore
import Definitions.Def_DetDLP_W3_ModMul
import Definitions.Def_DetDLP_M3A_FpWireCore
import Definitions.Def_DetDLP_M3A_FpPolyDefs

set_option autoImplicit false

open DetDLP DetDLP.M3A Groundwork

/-- From the native fp `CoreFamily`, produce per-query `WireCore` witnesses whose
    `fpBuild`/`fpEntry` packets match the wire-family obligations for some
    polynomial degree budget `c`. -/

theorem DetDLP.w3_fp_polywire_query_witness (mul : w3_modMulInterface)
    (hcore : FpWireCore.CoreFamily) :
    ∃ c : ℕ, 0 < c ∧
      ∀ q, w3_fpQueries q → ∃ W : w3_WireCore q 1000000,
        FpPolyDefs.fpBuild q.input = w3_wirePacket W ∧
        W.G.subdivision.nV ≤ (W.S + W.desc.length + 1) ^ c ∧
        ∀ (v : Fin W.G.subdivision.nV) (a : Fin (W.G.subdivision.deg v) → Bool),
          let w := encodePortQuery W.desc v.val (List.ofFn a)
          w.length + 1 ≤ (W.S + W.desc.length + 1) ^ c ∧
          EncodesTruncPoly (w3_precision q) (w3_len q) (FpPolyDefs.fpEntry w)
            (w3_liftTensor W.G W.T v a) := by sorry
