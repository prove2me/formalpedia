-- Prove2me | Theorems.Thm_BitDFT_shared_alphabet_multiplier_run
-- name    : BitDFT.shared_alphabet_multiplier_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T08:58:42.817871+00:00
-- url     : https://prove2.me/theorems/30505377-1b54-4079-9dfa-57bcf09bb95f
-- title:
--   Preserve the multiplier run in the shared child alphabet
-- statement:
--   Let A be a child machine and M a supplied multiplier. Embed M in the common product alphabet, pad its tape layout to the larger width, and preserve arbitrary caller data on the added tapes. The resulting multiplier stage follows M for exactly the same number of steps, with the final common-layout configuration equal to the corresponding embedding of M's final configuration.
-- source:
--   The common-alphabet run interface needed to stage and execute multiplier calls in the Fourier output-rescaling machine.

import Definitions.Def_BitDFT_SharedAlphabetStages
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_count_transport_correct
set_option autoImplicit false
open IntMul BitDFT.SharedAlphabetStages BitDFT.AlphabetEmbedding

theorem BitDFT.shared_alphabet_multiplier_run (A M : MultitapeTM)
    (extraCells : Fin (width A M) → ℕ → (BitDFT.SharedAlphabet.carrier A M).Sym)
    (extraHeads : Fin (width A M) → ℕ) (c : M.Cfg) (t : ℕ) :
    (right A M).step^[t] (rightConfig A M extraCells extraHeads c) =
      rightConfig A M extraCells extraHeads (M.step^[t] c) := by sorry
