-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_sum_iN_tops
-- name    : Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.sum_iN_tops
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:55:41.56126+00:00
-- url     : https://prove2.me/theorems/ff2ec820-0225-4e41-a1d9-e7f35f84794a
-- title:
--   Parity Sums Over Filtered Pairs: sum i N tops
-- statement:
--   The Parity Sums Over Filtered Pairs construction uses the sum i N tops property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean#L164-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean#L164-L168

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

theorem Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.sum_iN_tops [NeZero ν] (β : KapI ν r1 E →₀ ℕ) (TT : Finset (ZMod (2 * ν)))
    (h2 : ∀ k, β k ≠ 0 → k.1 ∈ TT) :
    ∑ s ∈ TT, ∑ e' ∈ range E, iN β s e' = ∑ k, β k := by sorry
