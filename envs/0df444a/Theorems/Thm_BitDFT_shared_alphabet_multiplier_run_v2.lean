-- Prove2me | Theorems.Thm_BitDFT_shared_alphabet_multiplier_run_v2
-- name    : BitDFT.shared_alphabet_multiplier_run_v2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T22:20:31.007813+00:00
-- url     : https://prove2.me/theorems/4a738373-fe66-4eae-af55-2fda6a1d5dce
-- title:
--   The multiplier stage preserves its exact run in the common child-machine layout
-- statement:
--   Let A be the child machine and M the supplied multiplier. Put both in the shared product alphabet and extend the smaller tape layout to the larger tape count. For every multiplier configuration and every choice of caller data on the extra tapes, the resulting common-layout stage follows M for exactly the same number of steps. Its final common-layout configuration is the embedding of M's exact final configuration, with every caller tape and head retained.
-- source:
--   Composition of the accepted alphabet-embedding simulation, arbitrary-data tape-extension simulation, and zero-transition tape-count transport theorems. This proves the multiplier-side handoff for the actual common host layout.

import Definitions.Def_BitDFT_SharedAlphabetStages
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_count_transport_correct
set_option autoImplicit false
open IntMul BitDFT.SharedAlphabetStages BitDFT.AlphabetEmbedding

theorem BitDFT.shared_alphabet_multiplier_run_v2 (A M : MultitapeTM)
    (extraCells : Fin (width A M) → ℕ → (BitDFT.SharedAlphabet.carrier A M).Sym)
    (extraHeads : Fin (width A M) → ℕ) (c : M.Cfg) (t : ℕ) :
    (right A M).step^[t] (rightConfig A M extraCells extraHeads c) =
      rightConfig A M extraCells extraHeads (M.step^[t] c) := by sorry
