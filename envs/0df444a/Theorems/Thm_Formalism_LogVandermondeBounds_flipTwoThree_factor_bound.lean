-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_factor_bound
-- name    : Formalism.LogVandermondeBounds.flipTwoThree.factor_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:53:05.602095+00:00
-- url     : https://prove2.me/theorems/a43f412f-366f-49b8-82fd-fd601ba5e3bf
-- title:
--   flip Two Three: factor bound
-- statement:
--   The flip Two Three construction uses the factor bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L85-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L85-L98

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

theorem Formalism.LogVandermondeBounds.flipTwoThree.factor_bound {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu)
    (i j : Fin n) (y : ℤ) (hy : y ∈ Iset lam (B0 lam nu) i) :
    |nu j - (j : ℤ) - (y - (i : ℤ))| ≤ lam 0 - lam (Fin.last n) + n + 1 := by sorry
