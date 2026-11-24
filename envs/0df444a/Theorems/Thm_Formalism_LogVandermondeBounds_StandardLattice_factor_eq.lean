-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_factor_eq
-- name    : Formalism.LogVandermondeBounds.StandardLattice.factor_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:57.950249+00:00
-- url     : https://prove2.me/theorems/7ed51ddd-4618-44a5-b2f3-e66c156ea737
-- title:
--   Standard Lattice: factor eq
-- statement:
--   The Standard Lattice construction uses the factor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/CardStabilizerVector.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/CardStabilizerVector.lean#L17-L21

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

theorem Formalism.LogVandermondeBounds.StandardLattice.factor_eq (q : ℝ) (hq : q ≠ 0) (n i : ℕ) (hi : i ≤ n) :
    q ^ n - q ^ i = q ^ n * (1 - q⁻¹ ^ (n - i)) := by sorry
