-- Prove2me | Theorems.Thm_DetDLP_m3b_ec_decoded_dimensions
-- name    : DetDLP.m3b_ec_decoded_dimensions
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T22:03:21.896643+00:00
-- url     : https://prove2.me/theorems/9ecf843d-0921-4e35-ab4c-0576f8d68be7
-- title:
--   The numeric EC packet fields decode the native query dimensions
-- statement:
--   Parsing the native descriptor recovers the prime bit length, block count, address width, dyadic precision, and truncation length used by the mathematical wire query.
-- source:
--   Supporting lemma for DetDLP.w3_ec_native_wire_programs, Section 4.2 (pp. 14–15).

import Definitions.Def_DetDLP_M3B_ECPolyDefs
import Definitions.Def_DetDLP_W3_Separator
open DetDLP DetDLP.M3B.ECPolyDefs

theorem DetDLP.m3b_ec_decoded_dimensions (q : w3_Query) (hq : w3_ecQueries q) :
    let t := dimensions q.input
    t.1 = q.b ∧ t.2.1 = q.m ∧ t.2.2.1 = q.k ∧ t.2.2.2.2.1 = w3_precision q ∧ t.2.2.2.2.2 = w3_len q := by sorry
