-- Prove2me | Theorems.Thm_DetDLP_w3_m5_modmul_r2
-- name    : DetDLP.w3_m5_modmul_r2
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T21:38:38.094797+00:00
-- url     : https://prove2.me/theorems/185dc955-67c0-4a8e-be97-51e5b72c4dab
-- title:
--   R2: unique modular multiplication witnesses on the numbered M5 graph
-- statement:
--   For canonical residues $x,y,z<q\le2^d$, the M5 multiplier has exactly one extension of the modular relation and no spurious extension. At $q=2^d$ the only product is the full $2d$-bit product, with its low $d$ bits pinned to $z$. At $q<2^d$ an additional $d$-bit quotient and a second full product enforce Euclidean division. Uniqueness includes all physical edge bits of the relevant numbered M5 copies.
-- source:
--   Deterministic Discrete Logarithms, §4.1–4.3, equations (4.1)–(4.5) and proof of Theorem 1.1, pp. 13–16; referee revisions R1 and R2.

import Definitions.Def_DetDLP_W3_ModMul
set_option autoImplicit false
open DetDLP DetDLP.w4_M5GraphBounds DetDLP.w4_M5PortTensor DetDLP.w4_ConvolutionArithmetic

theorem DetDLP.w3_m5_modmul_r2 : w3_modMulInterface := by sorry
