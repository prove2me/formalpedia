-- Prove2me | Theorems.Thm_DetDLP_s8h_ec_order_query
-- name    : DetDLP.s8h_ec_order_query
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T05:38:54.411325+00:00
-- url     : https://prove2.me/theorems/f0e81f0e-6143-4672-a126-0c2b5aa2d552
-- title:
--   Elliptic curve order query as a parsimonious tensor network
-- statement:
--   For tag 0, the number of solutions is the cardinality of the elliptic curve, including its point at infinity. Assuming the arithmetic gadget laws, construct uniform polynomial-time graph and port encoders for all valid queries of this tag. The encoded bipartite tensor network must realize this count parsimoniously and satisfy the size, scale, and maximum-degree bounds of the query specification.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8C_TagSpec
set_option autoImplicit false

theorem DetDLP.s8h_ec_order_query : DetDLP.S8C.GadgetLaws → DetDLP.S8C.TagSpec [0] := by sorry
