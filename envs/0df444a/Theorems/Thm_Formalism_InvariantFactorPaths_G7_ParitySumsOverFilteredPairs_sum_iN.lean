-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_sum_iN
-- name    : Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.sum_iN
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:45.868168+00:00
-- url     : https://prove2.me/theorems/05c466da-ebfb-4799-b830-926f956ca1a9
-- title:
--   Parity Sums Over Filtered Pairs: sum i N
-- statement:
--   The Parity Sums Over Filtered Pairs construction uses the sum i N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean#L53-L60

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
variable {ν r0 r1 E : ℕ}

theorem Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.sum_iN [NeZero ν] (β : KapI ν r1 E →₀ ℕ) (A : Finset (ZMod (2 * ν))) :
    ∑ s ∈ A, ∑ e' ∈ range E, iN β s e' =
      ∑ k ∈ univ.filter (fun k : KapI ν r1 E => k.1 ∈ A), β k := by sorry
