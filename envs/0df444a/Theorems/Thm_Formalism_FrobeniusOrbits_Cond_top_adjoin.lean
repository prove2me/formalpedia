-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Cond_top_adjoin
-- name    : Formalism.FrobeniusOrbits.Cond.top_adjoin
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:11:29.173306+00:00
-- url     : https://prove2.me/theorems/76480bbc-0fdc-462b-9943-4dc9225fc2bd
-- title:
--   Cond: top adjoin
-- statement:
--   The Cond construction uses the top adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L151-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L151-L153

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

theorem Formalism.FrobeniusOrbits.Cond.top_adjoin (m : ℕ) [NeZero m] : IntermediateField.adjoin ℚ ({z m} : Set (Cyc m)) = ⊤ := by sorry
