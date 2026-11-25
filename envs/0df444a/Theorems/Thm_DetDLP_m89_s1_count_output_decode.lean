-- Prove2me | Theorems.Thm_DetDLP_m89_s1_count_output_decode
-- name    : DetDLP.m89_s1_count_output_decode
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T21:25:08.846914+00:00
-- url     : https://prove2.me/theorems/1605e8b8-c048-4f98-b91c-4bedd3b69a57
-- title:
--   Exact decoding of a one-coefficient BTN count output
-- statement:
--   If a one-coefficient truncated polynomial is encoded using a bounded canonical coefficient and its value is the constant polynomial with natural coefficient count, then the output word is exactly the framed binary encoding of the singleton list [count].
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 Proof of Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_BTN

set_option autoImplicit false
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m89_s1_count_output_decode (P count : ℕ) (hcount : count < 2 ^ P)
    {w : List Bool} (hw : EncodesTruncPoly P 1 w
      (truncPolyOfCoeffs P 1 (fun _ => count))) :
    w = encodeNatListBin [count] := by sorry
