-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_sum_filter_fst
-- name    : Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.sum_filter_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:55:21.135342+00:00
-- url     : https://prove2.me/theorems/a740d215-a294-4a72-b9d7-98fb72f9c2ba
-- title:
--   Parity Sums Over Filtered Pairs: sum filter fst
-- statement:
--   The Parity Sums Over Filtered Pairs construction uses the sum filter fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean#L17-L23

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs

theorem Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.sum_filter_fst {A B M : Type*} [Fintype A] [Fintype B] [DecidableEq A] [AddCommMonoid M]
    (S : Finset A) (f : A × B → M) :
    ∑ x ∈ univ.filter (fun x : A × B => x.1 ∈ S), f x = ∑ s ∈ S, ∑ y, f (s, y) := by sorry
