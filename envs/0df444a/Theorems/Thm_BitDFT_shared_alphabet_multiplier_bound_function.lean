-- Prove2me | Theorems.Thm_BitDFT_shared_alphabet_multiplier_bound_function
-- name    : BitDFT.shared_alphabet_multiplier_bound_function
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T09:46:46.734262+00:00
-- url     : https://prove2.me/theorems/c81c490d-6d07-46ab-aaa9-4a4f3d1c641f
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

theorem BitDFT.shared_alphabet_multiplier_bound_function (A M : MultitapeTM) (T : ℕ → ℝ)
    (hM : BitDFT.Multiplier M T) : BitDFT.Multiplier (right A M) T := by sorry
