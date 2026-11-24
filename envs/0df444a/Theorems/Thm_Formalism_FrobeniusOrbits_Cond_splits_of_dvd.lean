-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Cond_splits_of_dvd
-- name    : Formalism.FrobeniusOrbits.Cond.splits_of_dvd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:10:40.718773+00:00
-- url     : https://prove2.me/theorems/7a32bce1-fd6a-4c43-b315-89f5de6fce77
-- title:
--   Cond: splits of dvd
-- statement:
--   The Cond construction uses the splits of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L114-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L114-L124

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

theorem Formalism.FrobeniusOrbits.Cond.splits_of_dvd {L K : Type*} [Field L] [Field K] [Algebra ℚ L] [Algebra ℚ K] (x : L)
    (f : ℚ[X]) (hf : f ≠ 0) (hx : aeval x f = 0) (hs : (f.map (algebraMap ℚ K)).Splits) :
    IsIntegral ℚ x ∧ ((minpoly ℚ x).map (algebraMap ℚ K)).Splits := by sorry
