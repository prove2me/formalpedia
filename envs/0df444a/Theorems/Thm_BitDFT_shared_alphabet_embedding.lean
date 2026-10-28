-- Prove2me | Theorems.Thm_BitDFT_shared_alphabet_embedding
-- name    : BitDFT.shared_alphabet_embedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T22:13:02.480442+00:00
-- url     : https://prove2.me/theorems/4c51e6a4-a464-43b8-9882-2d3f0416be35
-- title:
--   Both component machines run at the same clock over the shared alphabet
-- statement:
--   For any two fixed multitape machines, their product alphabet supports embeddings of both machines. Starting from any encoded configuration, each embedded machine performs exactly the same number of transitions as its original machine, with the complete configuration and halting output preserved. This provides a common alphabet for composing the arbitrary Fourier child with the supplied multiplier without adding runtime overhead.
-- source:
--   Specialization of the accepted exact alphabet-embedding simulation theorem to the published finite product alphabet. It proves a composition adapter only; it does not instantiate or close the full output-rescaling machine.

import Definitions.Def_BitDFT_SharedAlphabet
import Theorems.Thm_BitDFT_alphabet_embedding_correct
set_option autoImplicit false
open IntMul BitDFT.AlphabetEmbedding BitDFT.SharedAlphabet

theorem BitDFT.shared_alphabet_embedding (A M : MultitapeTM) :
    (∀ (c : A.Cfg) (t : ℕ),
      (machine (left A M)).step^[t]
          (BitDFT.AlphabetEmbedding.embed (left A M) c) =
        BitDFT.AlphabetEmbedding.embed (left A M) (A.step^[t] c)) ∧
    (∀ (x y : List Bool) (t : ℕ) (w : List Bool),
      A.HaltsWithOutput x y t w →
        (machine (left A M)).HaltsWithOutput x y t w) ∧
    (∀ (c : M.Cfg) (t : ℕ),
      (machine (right A M)).step^[t]
          (BitDFT.AlphabetEmbedding.embed (right A M) c) =
        BitDFT.AlphabetEmbedding.embed (right A M) (M.step^[t] c)) ∧
    (∀ (x y : List Bool) (t : ℕ) (w : List Bool),
      M.HaltsWithOutput x y t w →
        (machine (right A M)).HaltsWithOutput x y t w) := by sorry
