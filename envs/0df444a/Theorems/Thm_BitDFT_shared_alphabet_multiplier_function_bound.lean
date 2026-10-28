-- Prove2me | Theorems.Thm_BitDFT_shared_alphabet_multiplier_function_bound
-- name    : BitDFT.shared_alphabet_multiplier_function_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T09:43:35.383122+00:00
-- url     : https://prove2.me/theorems/19f23a51-ca3f-4889-aa61-6c080b58eea7
-- title:
--   Preserve a uniform multiplier time bound in the common layout
-- statement:
--   Let $M$ be a multiplier with a uniform time bound $T(q)$ for every input width $q$, and let $A$ be the Fourier-side machine. The common-alphabet embedding of $M$, padded to the shared tape width, remains a multiplier with the same uniform bound $T(q)$ at every width. The change of alphabet and tape representation adds no runtime.
-- source:
--   Uniform form of the accepted exact-width multiplier-bound transfer, intended for the rescaling machine theorem which assumes a bound function.

import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_BitDFT_Encoding
import Definitions.Def_BitDFT_SharedAlphabetStages
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_count_transport_correct
import Mathlib.Tactic
set_option autoImplicit false
open IntMul BitDFT.SharedAlphabetStages BitDFT.AlphabetEmbedding
private theorem tape_count_halts_iff (M : MultitapeTM) (n : ℕ) (h : M.k = n)
    (x y : List Bool) (t : ℕ) (w : List Bool) :
    (BitDFT.TapeCountTransport.machine M n h).HaltsWithOutput x y t w ↔
      M.HaltsWithOutput x y t w := by
  cases h
  rfl

theorem BitDFT.shared_alphabet_multiplier_function_bound (A M : MultitapeTM) (T : ℕ → ℝ)
    (hM : BitDFT.Multiplier M T) : BitDFT.Multiplier (right A M) T := by sorry
