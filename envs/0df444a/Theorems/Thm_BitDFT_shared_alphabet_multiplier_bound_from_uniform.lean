-- Prove2me | Theorems.Thm_BitDFT_shared_alphabet_multiplier_bound_from_uniform
-- name    : BitDFT.shared_alphabet_multiplier_bound_from_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T09:36:14.678651+00:00
-- url     : https://prove2.me/theorems/8284ecf0-5498-4baf-aa47-55d020c91355
-- title:
--   Transfer the full multiplier time function to the common layout
-- statement:
--   Let $M$ be a multiplier with a uniform time bound $T(q)$ for every input width $q$, and let $A$ be the Fourier-side machine. The common-alphabet embedding of $M$, padded to the shared tape width, remains a multiplier with the same uniform bound $T(q)$ at every width. The change of alphabet and tape representation adds no runtime.
-- source:
--   Uniform form of the accepted exact-width multiplier-bound transfer, intended for the rescaling machine theorem which assumes a bound function.

import Definitions.Def_BitDFT_Encoding
import Definitions.Def_BitDFT_SharedAlphabetStages
import Theorems.Thm_BitDFT_shared_alphabet_multiplier_bound
set_option autoImplicit false
open IntMul BitDFT.SharedAlphabetStages

theorem BitDFT.shared_alphabet_multiplier_bound_from_uniform (A M : MultitapeTM) (T : ℕ → ℝ)
    (hM : Multiplier M T) : Multiplier (right A M) T := by sorry
