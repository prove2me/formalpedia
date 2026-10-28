-- Prove2me | Theorems.Thm_BitDFT_shared_alphabet_child_run
-- name    : BitDFT.shared_alphabet_child_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T22:23:10.274004+00:00
-- url     : https://prove2.me/theorems/4cd0a48e-ddb7-4341-9286-02df7658b024
-- title:
--   The child stage preserves its exact run in the common multiplier layout
-- statement:
--   Let A be a child machine and M an integer multiplier. Embed A in their common product alphabet and extend its tapes to the larger of the two tape counts. For any A-configuration, any parked data and heads on added tapes, and any number of steps, the common-layout stage reaches exactly the embedding of A's original final configuration at that same clock. The added caller data remains intact.
-- source:
--   Composition of the exact alphabet-embedding run theorem, the arbitrary-data tape-extension theorem, and the zero-transition tape-count transport theorem. Together with the companion multiplier-stage result, this provides both sides of the common-host handoff used by the rescaling wrapper.

import Definitions.Def_BitDFT_SharedAlphabetStages
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_count_transport_correct
set_option autoImplicit false
open IntMul BitDFT.SharedAlphabetStages BitDFT.AlphabetEmbedding

theorem BitDFT.shared_alphabet_child_run (A M : MultitapeTM)
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
