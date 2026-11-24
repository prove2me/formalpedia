-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Cond_sqrt_exists
-- name    : Formalism.FrobeniusOrbits.Cond.sqrt_exists
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:10:27.902844+00:00
-- url     : https://prove2.me/theorems/444400fb-c810-4246-b410-458a12cee936
-- title:
--   Cond: sqrt exists
-- statement:
--   The Cond construction uses the sqrt exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L147-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L147-L149

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond

theorem Formalism.FrobeniusOrbits.Cond.sqrt_exists {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) {N : ℕ} [NeZero N] (hp : p ∣ N) :
    ∃ g : Cyc N, g ^ 2 = -(p : Cyc N) := by sorry
