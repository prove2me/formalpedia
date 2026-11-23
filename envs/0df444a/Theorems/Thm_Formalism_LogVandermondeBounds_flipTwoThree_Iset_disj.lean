-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_Iset_disj
-- name    : Formalism.LogVandermondeBounds.flipTwoThree.Iset_disj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:40:43.14502+00:00
-- url     : https://prove2.me/theorems/485462bd-e5f3-4587-a44c-a1662eb6a16d
-- title:
--   flip Two Three: Iset disj
-- statement:
--   The flip Two Three construction uses the Iset disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L35-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L35-L52

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

theorem Formalism.LogVandermondeBounds.flipTwoThree.Iset_disj {n : ℕ} {lam : Fin (n + 1) → ℤ} (ha : Antitone lam) (b : ℤ) (i j : Fin n)
    (hij : i ≠ j) :
    Disjoint ((Iset lam b i).image (fun y => y - (i : ℤ)))
      ((Iset lam b j).image (fun y => y - (j : ℤ))) := by sorry
