-- Prove2me | Theorems.Thm_BitDFT_ReaderHostFrame_tracked_input_word_embeds
-- name    : BitDFT.ReaderHostFrame.tracked_input_word_embeds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T18:41:05.736262+00:00
-- url     : https://prove2.me/theorems/ad44bf23-f673-428d-a9cd-ebdfcd279d32
-- title:
--   Tagged multiplier operands embed as the host input word
-- statement:
--   For binary operands $x$ and $y$, the tracked multiplier encodes each bit with its visited tag and places a separator between the operands. Under the multiplier alphabet embedding into the shared host, those symbols become exactly the host-alphabet word $x#y$. This identifies the content of the staged buffer with the tracked call interface.
-- source:
--   The result follows from the zero, one, and separator preservation laws of the alphabet embedding, applied pointwise to the two input words.

import Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace BitDFT.ReaderHostFrame
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost

theorem tracked_input_word_embeds (A M H : MultitapeTM) (x y : List Bool) :
    ((TrackedBankPreparation.inputWord M x y).map
        (fun s : M.Sym => some (s, true))).map
        (TripleAlphabet.multiplier A (tracked M) H).encode =
      x.map (host A M H).bitSym ++ (host A M H).sep :: y.map (host A M H).bitSym := by sorry
