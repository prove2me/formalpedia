-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_one_le_dAof_right
-- name    : Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.one_le_dAof_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:25.614799+00:00
-- url     : https://prove2.me/theorems/674c912c-f1c5-4358-ae80-746849cd0602
-- title:
--   Parity Sums Over Filtered Pairs: one le d Aof right
-- statement:
--   The Parity Sums Over Filtered Pairs construction uses the one le d Aof right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean#L68-L72

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

theorem Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.one_le_dAof_right {p : ℕ} (hp : 0 < p) (φ : PhiI ν r0 r1 E) :
    1 ≤ dAof p φ (pairSecond φ, φ.2.2.2.2) := by sorry
