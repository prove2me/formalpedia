-- Prove2me | Theorems.Thm_DetDLP_s8i_ec_moment_query
-- name    : DetDLP.s8i_ec_moment_query
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T05:03:42.641396+00:00
-- url     : https://prove2.me/theorems/6543b4e5-91f6-4423-8dcc-3fa4036f7731
-- title:
--   EC moment query reduction
-- statement:
--   Under the stated gadget laws, the elliptic-curve query reduction realizes the requested single query tag.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8C_TagSpec
set_option autoImplicit false

theorem DetDLP.s8i_ec_moment_query : DetDLP.S8C.GadgetLaws → DetDLP.S8C.TagSpec [2] := by sorry
