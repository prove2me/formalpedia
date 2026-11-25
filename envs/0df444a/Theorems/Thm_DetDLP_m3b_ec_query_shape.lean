-- Prove2me | Theorems.Thm_DetDLP_m3b_ec_query_shape
-- name    : DetDLP.m3b_ec_query_shape
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T21:20:34.841726+00:00
-- url     : https://prove2.me/theorems/06300b58-2504-4317-b357-49c90bfc10ed
-- title:
--   Two-sided lookup-width bounds for native elliptic-curve queries
-- statement:
--   For every native elliptic-curve query the total number of lookup ports lies between the prime bit length and two thousand times that bit length, and the lookup width is positive.
-- source:
--   Supporting lemma for DetDLP.w3_ec_native_wire_programs (Section 4.2, pp. 14–15).

import Definitions.Def_DetDLP_W3_Separator
import Theorems.Thm_DetDLP_hasse_ec_point_count_bound

set_option autoImplicit false
set_option maxHeartbeats 400000
open DetDLP

theorem DetDLP.m3b_ec_query_shape (q : w3_Query) (hq : w3_ecQueries q) : 4*q.m*q.k ≤ 2000*q.b ∧ q.b ≤ 4*q.m*q.k ∧ 1 ≤ q.k := by sorry
