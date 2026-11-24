-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Cond_splits_pow
-- name    : Formalism.FrobeniusOrbits.Cond.splits_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:10:36.843889+00:00
-- url     : https://prove2.me/theorems/ce99467a-6720-487c-a18b-cf78b6de7609
-- title:
--   Cond: splits pow
-- statement:
--   The Cond construction uses the splits pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L126-L130

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

theorem Formalism.FrobeniusOrbits.Cond.splits_pow {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ} {ξ : K}
    (hξ : IsPrimitiveRoot ξ n) : ((X ^ n - 1 : ℚ[X]).map (algebraMap ℚ K)).Splits := by sorry
