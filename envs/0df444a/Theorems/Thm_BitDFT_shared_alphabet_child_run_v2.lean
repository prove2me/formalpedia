-- Prove2me | Theorems.Thm_BitDFT_shared_alphabet_child_run_v2
-- name    : BitDFT.shared_alphabet_child_run_v2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T09:02:10.368629+00:00
-- url     : https://prove2.me/theorems/1664a984-a006-4a63-973b-b7ac571437a7
-- title:
--   Preserve the child run in the shared multiplier alphabet
-- statement:
--   Let A be a child machine and M a supplied multiplier. Embed A in the common product alphabet, pad its tape layout to the larger width, and preserve arbitrary caller data on the added tapes. The resulting child stage follows A for exactly the same number of steps, with its final common-layout configuration equal to the corresponding embedding of A's final configuration.
-- source:
--   The child-side exact-clock interface needed to run the Fourier child before multiplier-based output rescaling in a single shared host.

import Definitions.Def_BitDFT_SharedAlphabetStages
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_count_transport_correct
set_option autoImplicit false
open IntMul BitDFT.SharedAlphabetStages BitDFT.AlphabetEmbedding

theorem BitDFT.shared_alphabet_child_run_v2 (A M : MultitapeTM)
    (extraCells : Fin (width A M) → ℕ → (BitDFT.SharedAlphabet.carrier A M).Sym)
    (extraHeads : Fin (width A M) → ℕ) (c : A.Cfg) (t : ℕ) :
    (left A M).step^[t]
      (BitDFT.TapeCountTransport.embed
        (BitDFT.TapeExtension.machine (BitDFT.AlphabetEmbedding.machine
          (BitDFT.SharedAlphabet.left A M)) (width A M - A.k))
        (width A M) (Nat.add_sub_of_le (Nat.le_max_left A.k M.k))
        (BitDFT.TapeExtension.embed
          (BitDFT.AlphabetEmbedding.machine (BitDFT.SharedAlphabet.left A M))
          (width A M - A.k)
          (fun i => extraCells (Fin.cast (Nat.add_sub_of_le (Nat.le_max_left A.k M.k)) i))
          (fun i => extraHeads (Fin.cast (Nat.add_sub_of_le (Nat.le_max_left A.k M.k)) i))
          (BitDFT.AlphabetEmbedding.embed (BitDFT.SharedAlphabet.left A M) c))) =
    BitDFT.TapeCountTransport.embed
      (BitDFT.TapeExtension.machine (BitDFT.AlphabetEmbedding.machine
        (BitDFT.SharedAlphabet.left A M)) (width A M - A.k))
      (width A M) (Nat.add_sub_of_le (Nat.le_max_left A.k M.k))
      (BitDFT.TapeExtension.embed
        (BitDFT.AlphabetEmbedding.machine (BitDFT.SharedAlphabet.left A M))
        (width A M - A.k)
        (fun i => extraCells (Fin.cast (Nat.add_sub_of_le (Nat.le_max_left A.k M.k)) i))
        (fun i => extraHeads (Fin.cast (Nat.add_sub_of_le (Nat.le_max_left A.k M.k)) i))
        (BitDFT.AlphabetEmbedding.embed (BitDFT.SharedAlphabet.left A M) (A.step^[t] c))) := by sorry
