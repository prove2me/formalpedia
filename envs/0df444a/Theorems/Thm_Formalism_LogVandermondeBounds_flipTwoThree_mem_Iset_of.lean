-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_mem_Iset_of
-- name    : Formalism.LogVandermondeBounds.flipTwoThree.mem_Iset_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:42.663693+00:00
-- url     : https://prove2.me/theorems/f792ce72-0171-40bc-a8f6-061b8bfdbaaa
-- title:
--   flip Two Three: mem Iset of
-- statement:
--   The flip Two Three construction uses the mem Iset of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L24-L33

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InterlacingSeparation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset

theorem Formalism.LogVandermondeBounds.flipTwoThree.mem_Iset_of {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu' : Fin n → ℤ} {b : ℤ}
    (h' : Interlace lam nu') (hb : B0 lam nu' = b) (i : Fin n) : nu' i ∈ Iset lam b i := by sorry
