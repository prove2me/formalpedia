-- Prove2me | Theorems.Thm_DetDLP_w3_ec_polywire_core_packet
-- name    : DetDLP.w3_ec_polywire_core_packet
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-25T03:30:56.438186+00:00
-- url     : https://prove2.me/theorems/21b3b8f9-80b3-4341-9e37-2c27c1525cc1
-- title:
--   EC polywire core packet/size/entry package
-- statement:
--   From per-query elliptic-curve wire-core existence, produce a polynomial degree budget together with matching ecBuild packet identity, subdivision-size bound, and EncodesTruncPoly for ecEntry.
-- source:
--   DetDLP milestone 8 polywire decomposition

import Definitions.Def_DetDLP_W3_WireCore
import Definitions.Def_DetDLP_W3_ModMul
import Definitions.Def_DetDLP_M3B_ECPolyDefs

set_option autoImplicit false

open DetDLP DetDLP.M3B.ECPolyDefs Groundwork

/-- From per-query ec wire-core existence, choose a degree budget and matching
    `ecBuild`/`ecEntry` packet witnesses. -/

theorem DetDLP.w3_ec_polywire_core_packet (mul : w3_modMulInterface)
    (hcore : ∀ q, w3_ecQueries q →
      ∃ W : w3_WireCore q 100000000, W.desc = q.input ∧ W.S = 100000000 * q.m * q.b) :
    ∃ c : ℕ, 0 < c ∧
      (∀ q, w3_ecQueries q → ∃ W : w3_WireCore q 100000000,
        ecBuild q.input = w3_wirePacket W) ∧
      (∀ q, w3_ecQueries q → ∀ W : w3_WireCore q 100000000,
        ecBuild q.input = w3_wirePacket W →
        W.G.subdivision.nV ≤ (W.S + W.desc.length + 1) ^ c) ∧
      (∀ q, w3_ecQueries q → ∀ W : w3_WireCore q 100000000,
        ecBuild q.input = w3_wirePacket W →
        ∀ (v : Fin W.G.subdivision.nV) (a : Fin (W.G.subdivision.deg v) → Bool),
          let w := encodePortQuery W.desc v.val (List.ofFn a)
          w.length + 1 ≤ (W.S + W.desc.length + 1) ^ c ∧
          EncodesTruncPoly (w3_precision q) (w3_len q) (ecEntry w)
            (w3_liftTensor W.G W.T v a)) := by sorry
