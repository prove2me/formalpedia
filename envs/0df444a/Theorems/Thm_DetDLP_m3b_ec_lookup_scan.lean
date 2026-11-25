-- Prove2me | Theorems.Thm_DetDLP_m3b_ec_lookup_scan
-- name    : DetDLP.m3b_ec_lookup_scan
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T22:10:17.159294+00:00
-- url     : https://prove2.me/theorems/4c2904a8-ebd2-426e-945a-76b59e395969
-- title:
--   Native EC lookup scans agree with the mathematical address table
-- statement:
--   The numeric scan of the serialized native EC blocks returns precisely the optional indexed label obtained from the mathematical lookup function, including the offset across preceding blocks.
-- source:
--   Supporting lemma for DetDLP.w3_ec_native_wire_programs, Section 4.2 (pp. 14–15).

import Definitions.Def_DetDLP_M3B_ECPolyDefs
import Definitions.Def_DetDLP_W3_NativeLookupWeight
open DetDLP M3B.ECPolyDefs

theorem DetDLP.m3b_ec_lookup_scan (q : w3_Query) (hq : w3_ecQueries q) (i : Fin q.m) (h : ℕ) :
    lookup (frames q.input) (dimensions q.input).2.2.2.1 i.val h = (w3_lookupIndex q i h).map (fun r => (q.y (q.FB.coordOf i r)).val) := by sorry
