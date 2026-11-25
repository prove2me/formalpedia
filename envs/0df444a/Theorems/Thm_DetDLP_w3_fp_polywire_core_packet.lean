-- Prove2me | Theorems.Thm_DetDLP_w3_fp_polywire_core_packet
-- name    : DetDLP.w3_fp_polywire_core_packet
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-25T03:35:30.241589+00:00
-- url     : https://prove2.me/theorems/b0b1193b-1e97-470a-ac3a-3dd1220c818b
-- title:
--   FP polywire core packet/size/entry package
-- statement:
--   From a native finite-field CoreFamily, produce a single polynomial degree budget together with per-query wire-core witnesses realizing the fpBuild packet identity, a uniform subdivision-size bound, and EncodesTruncPoly for fpEntry against the lifted gate tensor.
-- source:
--   DetDLP milestone 8 polywire decomposition

import Definitions.Def_DetDLP_W3_WireCore
import Definitions.Def_DetDLP_W3_ModMul
import Definitions.Def_DetDLP_M3A_FpWireCore
import Definitions.Def_DetDLP_M3A_FpPolyDefs

set_option autoImplicit false

open DetDLP DetDLP.M3A Groundwork

/-- From `CoreFamily`, choose a degree budget and, for each fp query, a wire-core
    whose terminal BTN packet equals `fpBuild q.input`. -/

theorem DetDLP.w3_fp_polywire_core_packet (mul : w3_modMulInterface)
    (hcore : FpWireCore.CoreFamily) :
    ∃ c : ℕ, 0 < c ∧
      (∀ q, w3_fpQueries q → ∃ W : w3_WireCore q 1000000,
        FpPolyDefs.fpBuild q.input = w3_wirePacket W) ∧
      (∀ q, w3_fpQueries q → ∀ W : w3_WireCore q 1000000,
        FpPolyDefs.fpBuild q.input = w3_wirePacket W →
        W.G.subdivision.nV ≤ (W.S + W.desc.length + 1) ^ c) ∧
      (∀ q, w3_fpQueries q → ∀ W : w3_WireCore q 1000000,
        FpPolyDefs.fpBuild q.input = w3_wirePacket W →
        ∀ (v : Fin W.G.subdivision.nV) (a : Fin (W.G.subdivision.deg v) → Bool),
          let w := encodePortQuery W.desc v.val (List.ofFn a)
          w.length + 1 ≤ (W.S + W.desc.length + 1) ^ c ∧
          EncodesTruncPoly (w3_precision q) (w3_len q) (FpPolyDefs.fpEntry w)
            (w3_liftTensor W.G W.T v a)) := by sorry
