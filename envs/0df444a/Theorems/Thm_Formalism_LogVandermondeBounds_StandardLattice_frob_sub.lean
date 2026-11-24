-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_frob_sub
-- name    : Formalism.LogVandermondeBounds.StandardLattice.frob_sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:26.019869+00:00
-- url     : https://prove2.me/theorems/29368539-bb96-445c-81e5-a36cf772157e
-- title:
--   Standard Lattice: frob sub
-- statement:
--   The Standard Lattice construction uses the frob sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InertPrimeCountBound.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InertPrimeCountBound.lean#L18-L25

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InertPrimeCountBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] {q : ℕ}

theorem Formalism.LogVandermondeBounds.StandardLattice.frob_sub (hq : Fintype.card L = q ^ 2) (a b : L) : (a - b) ^ q = a ^ q - b ^ q := by sorry
