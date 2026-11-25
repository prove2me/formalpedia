-- Prove2me | Theorems.Thm_DetDLP_w3_native_lookup_address
-- name    : DetDLP.w3_native_lookup_address
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T00:25:27.396943+00:00
-- url     : https://prove2.me/theorems/6d5badc8-0ce9-497a-af04-a5f8167e3d1d
-- title:
--   Injectivity and width of native lookup addresses
-- statement:
--   For a native prime-field or short Weierstrass query, let $F_i$ be an enumerated factor block and $k$ its address width. The prescribed address mapping on list positions is injective, and every address is strictly below $2^k$. Thus a physical lookup word uniquely identifies its list position when it is occupied, without assuming an ordering of the input block.
-- source:
--   Deterministic Discrete Logarithms, §4.1–4.3, equations (4.1)–(4.5) and proof of Theorem 1.1, pp. 13–16; referee revisions R1 and R2.

import Definitions.Def_DetDLP_W3_Separator
set_option autoImplicit false
open DetDLP

theorem DetDLP.w3_native_lookup_address (q : w3_Query) (hq : w3_fpQueries q ∨ w3_ecQueries q) :
    ∀ i : Fin q.m, Function.Injective (q.addr i) ∧ ∀ r, q.addr i r < 2^q.k := by sorry
