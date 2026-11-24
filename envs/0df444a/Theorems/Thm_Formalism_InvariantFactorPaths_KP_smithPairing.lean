-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_smithPairing
-- name    : Formalism.InvariantFactorPaths.KP.smithPairing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:07.630609+00:00
-- url     : https://prove2.me/theorems/5c84a9b9-c728-4ae3-b090-28dbc480b3a9
-- title:
--   KP: smith Pairing
-- statement:
--   The KP construction uses the smith Pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/BinomialRatio/SmithPairing.lean#L84-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/BinomialRatio/SmithPairing.lean#L84-L108

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_BinomialRatio_SmithPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP
open Module

theorem Formalism.InvariantFactorPaths.KP.smithPairing (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K) :
    ∃ P Q : Matrix (Fin n) (Fin n) O, IsUnit P.det ∧ IsUnit Q.det ∧
      ∀ i j, i ≠ j → (P.map (algebraMap O K) * G * Q.map (algebraMap O K)) i j = 0 := by sorry
