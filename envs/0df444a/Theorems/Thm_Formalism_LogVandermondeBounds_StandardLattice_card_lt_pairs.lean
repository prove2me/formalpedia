-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_card_lt_pairs
-- name    : Formalism.LogVandermondeBounds.StandardLattice.card_lt_pairs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:28:25.503481+00:00
-- url     : https://prove2.me/theorems/e098a86a-8296-48af-8d22-13be7c9b3ff5
-- title:
--   Standard Lattice: card lt pairs
-- statement:
--   The Standard Lattice construction uses the card lt pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/CardStabilizerVector.lean#L67-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/CardStabilizerVector.lean#L67-L77

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
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

theorem Formalism.LogVandermondeBounds.StandardLattice.card_lt_pairs (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by sorry
