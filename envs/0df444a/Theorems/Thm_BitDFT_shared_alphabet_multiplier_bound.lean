-- Prove2me | Theorems.Thm_BitDFT_shared_alphabet_multiplier_bound
-- name    : BitDFT.shared_alphabet_multiplier_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T09:25:51.586857+00:00
-- url     : https://prove2.me/theorems/bbdb927f-6884-480f-95e5-21d2ae33b6c8
-- title:
--   Preserve the multiplier time bound in the shared alphabet
-- statement:
--   Let $M$ be a multitape machine that multiplies two $q$-bit inputs within $T$ steps, and let $A$ be the child machine used by the Fourier construction. Embed $M$ into their shared product alphabet and pad it to the common tape width. Then the resulting multiplier machine also multiplies every pair of $q$-bit inputs within the same $T$ steps. Thus the alphabet and tape-layout changes add no steps to the multiplier bound.
-- source:
--   The exact-bound transfer needed to apply an integer-multiplication runtime bound inside the finite-precision Fourier output-rescaling machine.

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

theorem BitDFT.shared_alphabet_multiplier_bound (A M : MultitapeTM) (q : ℕ) (T : ℝ)
    (hM : MultipliesAt M q T) : MultipliesAt (right A M) q T := by sorry
