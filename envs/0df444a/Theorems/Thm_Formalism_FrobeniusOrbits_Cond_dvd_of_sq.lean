-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Cond_dvd_of_sq
-- name    : Formalism.FrobeniusOrbits.Cond.dvd_of_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:11:31.519786+00:00
-- url     : https://prove2.me/theorems/b257d2e7-7f19-4270-9ddf-9425bcc9e8f5
-- title:
--   Cond: dvd of sq
-- statement:
--   The Cond construction uses the dvd of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L210-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L210-L249

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

theorem Formalism.FrobeniusOrbits.Cond.dvd_of_sq {p : ℕ} [hp : Fact p.Prime] (hp4 : p % 4 = 3) {m : ℕ} [NeZero m] (y : Cyc m)
    (hy : y ^ 2 = -(p : Cyc m)) : p ∣ m := by sorry
