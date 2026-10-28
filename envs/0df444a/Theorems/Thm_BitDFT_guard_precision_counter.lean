-- Prove2me | Theorems.Thm_BitDFT_guard_precision_counter
-- name    : BitDFT.guard_precision_counter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:53:13.035989+00:00
-- url     : https://prove2.me/theorems/8accdf7c-1f52-4add-8296-6010b56a486f
-- title:
--   The counter computes guard-precision arithmetic within 5q transitions
-- statement:
--   Let b≥1, let w be a binary encoding of b with at most b bits, and set q=b+3 lg(n)+5. Starting with the reversed binary word on the binary work tape and 3 lg(n)+5 unary marks on the count tape, the explicit binary-counter machine halts within 5q transitions with a little-endian representation of q. Its unary tape is cleared and its head positions and unchanged caller data are specified exactly. This is the arithmetic stage after preparing the parsed bits and unary increment; it does not claim to parse n, construct that increment, or serialize the resulting header.
-- source:
--   Specialization of BitDFT.binary_counter_add to the Fourier guard precision. The little-endian value of a reversed word equals the existing IntMul.val encoding. Preparing and serializing the counter inputs remain distinct machine constructions.

import Definitions.Def_BitDFT_BinaryCounter
import Definitions.Def_BitDFT_Numerics
open BitDFT BitDFT.BinaryCounter IntMul

theorem BitDFT.guard_precision_counter (base : machine.Cfg) (n b : ℕ) (w : List Bool)
    (hb : 1 ≤ b) (hv : IntMul.val w = b) (hw : w.length ≤ b) :
    ∃ t v, t ≤ 5*guardPrecision n b ∧ BinaryCounter.value v = guardPrecision n b ∧
      machine.step^[t] (frame base .tick w.reverse (3*IntMul.lg n+5) 1) =
        frame base .halt v 0 1 := by sorry
