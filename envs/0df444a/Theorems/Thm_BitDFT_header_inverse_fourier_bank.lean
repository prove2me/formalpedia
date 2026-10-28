-- Prove2me | Theorems.Thm_BitDFT_header_inverse_fourier_bank
-- name    : BitDFT.header_inverse_fourier_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T15:49:41.194723+00:00
-- url     : https://prove2.me/theorems/c62d01bc-b57e-499e-99c3-829bd73384b7
-- title:
--   Fourier tapes are appended tapes in the header reader frame
-- statement:
--   The shared tape layout routes the Fourier work bank before the header-reader bank. Consequently, when the header reader is the active component, every non-input Fourier tape address is supplied by its appended, preserved bank. Formally, for any non-input address p in the Fourier machine’s bank, the inverse header routing sends p to an appended-bank index at least H.k.
-- source:
--   The proof computes the cyclic routing inverse explicitly. It supplies the disjoint-bank condition needed to compose a Fourier coordinate-reader configuration with the parsed dimension in one common host frame.

import Definitions.Def_BitDFT_BankedTripleAlphabetHost
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost

theorem BitDFT.header_inverse_fourier_bank (A M H : IntMul.MultitapeTM)
    (p : Fin (width A M H)) (hp : 1 ≤ p.val) (hpa : p.val < A.k) :
    H.k ≤ ((route A M H (headerOffset A M H)
      (by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
          dsimp [tail, headerOffset]; omega) ).symm p).val := by sorry
