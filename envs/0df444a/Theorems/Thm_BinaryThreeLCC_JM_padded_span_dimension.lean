-- Prove2me | Theorems.Thm_BinaryThreeLCC_JM_padded_span_dimension
-- name    : BinaryThreeLCC.JM.padded_span_dimension
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:02:51.685673+00:00
-- url     : https://prove2.me/theorems/251232fc-f904-46a0-92d4-abd33551d88d
-- title:
--   Padded rows of an injective binary linear code span $\mathbb F_2^k$
-- statement:
--   Let $C:\mathbb F_2^k\to\mathbb F_2^n$ be an injective $\mathbb F_2$-linear encoding, and for $u\in[n]$ let $v_u\in\mathbb F_2^k$ be its $u$-th row, so that $C(b)_u=\langle v_u,b\rangle$. Pad the rows to the index set $[2n]$ by setting $v_u:=0$ for $u\in[2n]\setminus[n]$. Then
--
--   $$\dim_{\mathbb F_2}\operatorname{span}\{v_u : u\in[2n]\}=k .$$
--
--   This is the dimension count used at the start of Fact 2.1 and of the proof of Theorem 1: the quantity bounded by the whole argument is exactly the message dimension $k$.
--
--   **Formalization Note** The rows are `paddedRow C`, and the dimension is `spanDimension`, the `finrank` of the span of the range.
-- source:
--   Janzer–Manohar, Reed–Muller Codes are Optimal Binary Linear 3-Query LCCs, STOC 2027 submission #732, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf, Fact 2.1 (printed pp. 2–3: dim span{v_1,...,v_n} = k since C is injective; v_u := 0 for u in [2n]\[n])

import Definitions.Def_BinaryThreeLCC_Main_Matchings

set_option autoImplicit false

namespace BinaryThreeLCC.JM

open BinaryThreeLCC.Main

theorem padded_span_dimension {k n : ℕ} (C : CodeModel k n) :
    spanDimension (paddedRow C) = k := by sorry

end BinaryThreeLCC.JM
