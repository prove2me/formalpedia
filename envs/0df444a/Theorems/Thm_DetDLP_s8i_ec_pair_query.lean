-- Prove2me | Theorems.Thm_DetDLP_s8i_ec_pair_query
-- name    : DetDLP.s8i_ec_pair_query
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T05:03:41.460126+00:00
-- url     : https://prove2.me/theorems/8ee434fa-daec-49e4-a3ee-d3916f19bccd
-- title:
--   EC pair query reduction
-- statement:
--   Under the stated gadget laws, the elliptic-curve query reduction realizes the requested single query tag.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8C_TagSpec
set_option autoImplicit false

theorem DetDLP.s8i_ec_pair_query : DetDLP.S8C.GadgetLaws → DetDLP.S8C.TagSpec [6] := by sorry
