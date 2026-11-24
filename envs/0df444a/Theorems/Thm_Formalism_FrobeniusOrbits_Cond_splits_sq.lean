-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Cond_splits_sq
-- name    : Formalism.FrobeniusOrbits.Cond.splits_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:11:00.975654+00:00
-- url     : https://prove2.me/theorems/35051dfb-4ecf-448e-ade8-cd63ae60e7a2
-- title:
--   Cond: splits sq
-- statement:
--   The Cond construction uses the splits sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L132-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L132-L141

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

theorem Formalism.FrobeniusOrbits.Cond.splits_sq {K : Type*} [Field K] [Algebra ℚ K] (c : ℕ) (g : K) (hg : g ^ 2 = -(c : K)) :
    ((X ^ 2 + C (c : ℚ) : ℚ[X]).map (algebraMap ℚ K)).Splits := by sorry
