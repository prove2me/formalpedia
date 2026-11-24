-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_eArith_ge
-- name    : Formalism.InvariantFactorPaths.L4.eArith_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:12.023168+00:00
-- url     : https://prove2.me/theorems/94f949a9-22bd-444a-a916-617f94fbb00b
-- title:
--   L4: e Arith ge
-- statement:
--   The L4 construction uses the e Arith ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/EArith.lean#L7-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/EArith.lean#L7-L38

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Finset

theorem Formalism.InvariantFactorPaths.L4.eArith_ge : ∀ (s : ℕ) (ka : ℕ → ℤ) (β : ℕ → ℕ) (c : ℤ),
    (∀ i, i + 1 < s → ka (i + 1) + β (i + 1) ≤ ka i) → (0 < s → ka 0 + β 0 ≤ c) →
    (∑ a ∈ range s, (β a : ℤ)) ≤
      (c - (∑ a ∈ range s, (β a : ℤ)) + 1) * (∑ a ∈ range s, (β a : ℤ)) - (∑ a ∈ range s, (β a : ℤ) * ka a) +
        ∑ b ∈ range s, ∑ a ∈ range b, ((β a : ℤ) + 1) * (β b : ℤ) := by sorry
