-- Prove2me | Theorems.Thm_DetDLP_w3_ec_polywire_query_witness
-- name    : DetDLP.w3_ec_polywire_query_witness
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-25T00:28:32.01935+00:00
-- url     : https://prove2.me/theorems/c214a86c-160f-4184-b585-6cf8badaacbd
-- title:
--   DetDLP WireKit: w3 ec polywire query witness
-- statement:
--   From per-query elliptic-curve wire-core existence, produce matching `ecBuild`/`ecEntry` packet witnesses realizing the `w3_polyWireFamily` obligations at some polynomial degree budget.
-- source:
--   DetDLP WireKit deep-sketch private children (separator/polywire assemble)

import Definitions.Def_DetDLP_W3_WireCore
import Definitions.Def_DetDLP_W3_ModMul
import Definitions.Def_DetDLP_M3B_ECPolyDefs

set_option autoImplicit false

open DetDLP DetDLP.M3B.ECPolyDefs Groundwork

/-- From per-query ec wire-core existence, produce matching `ecBuild`/`ecEntry`
    packet witnesses for some polynomial degree budget `c`. -/

theorem DetDLP.w3_ec_polywire_query_witness (mul : w3_modMulInterface)
    (hcore : ∀ q, w3_ecQueries q →
      ∃ W : w3_WireCore q 100000000, W.desc = q.input ∧ W.S = 100000000 * q.m * q.b) :
    ∃ c : ℕ, 0 < c ∧
      ∀ q, w3_ecQueries q → ∃ W : w3_WireCore q 100000000,
        ecBuild q.input = w3_wirePacket W ∧
        W.G.subdivision.nV ≤ (W.S + W.desc.length + 1) ^ c ∧
        ∀ (v : Fin W.G.subdivision.nV) (a : Fin (W.G.subdivision.deg v) → Bool),
          let w := encodePortQuery W.desc v.val (List.ofFn a)
          w.length + 1 ≤ (W.S + W.desc.length + 1) ^ c ∧
          EncodesTruncPoly (w3_precision q) (w3_len q) (ecEntry w)
            (w3_liftTensor W.G W.T v a) := by sorry
