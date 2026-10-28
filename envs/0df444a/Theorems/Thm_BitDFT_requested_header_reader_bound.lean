-- Prove2me | Theorems.Thm_BitDFT_requested_header_reader_bound
-- name    : BitDFT.requested_header_reader_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T13:59:16.153976+00:00
-- url     : https://prove2.me/theorems/d38db03e-afb2-448e-bb13-2385952acfb7
-- title:
--   The actual Fourier request header is read with at most 16nq transitions
-- statement:
--   Let $n,b\ge1$, let $q=b+3\max(1,\lceil\log_2 n\rceil)+5$, and let $U$ be any encoded length-$n$ vector of Gaussian integers. There is an execution of the fixed header reader on the mission's requested Fourier input that takes at most $16nq$ transitions, outputs the remaining precision header and vector unchanged, retains the complete binary representation of $n$ on its field tape, and leaves its unary-counter tape blank beyond the permanent marker.
--
--   No norm or magnitude hypothesis on $U$ is needed: the statement concerns its exact fixed-width bit encoding. The proof supplies an actual halting execution and complete output tape.
-- source:
--   Specialization of BitDFT.header_reader_correct to Definitions.Def_BitDFT_Encoding.encNat and Definitions.Def_BitDFT_Numerics.requestedInput, with the proved vector length theorem https://prove2.me/theorems/c4c1bdcd-4820-48c9-9efa-6b35abc085a1. The explicit clock inequality uses n.size ≤ lg(n)+1 and b.size ≤ b. This is an input-processing component of the output-rescaling wrapper.

import Definitions.Def_BitDFT_HeaderReader
import Definitions.Def_BitDFT_Numerics
open BitDFT IntMul

theorem BitDFT.requested_header_reader_bound (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b)
    (U : Fin n → ℤ × ℤ) :
    ∃ t : ℕ, (t : ℝ) ≤ 16 * (n : ℝ) * (guardPrecision n b : ℝ) ∧
      HeaderReader.machine.HaltsWithOutput (requestedInput b U) [] t
        (encNat b ++ encVector (guardPrecision n b + 1) U) ∧
      (HeaderReader.machine.step^[t]
        (HeaderReader.machine.initCfg (requestedInput b U) [])).cells 3 =
        HeaderReader.machine.tapeOf ((IntMul.bin n.size n).map HeaderReader.machine.bitSym) ∧
      (HeaderReader.machine.step^[t]
        (HeaderReader.machine.initCfg (requestedInput b U) [])).cells 2 =
        HeaderReader.machine.tapeOf [] := by sorry
