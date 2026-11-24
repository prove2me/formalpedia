-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_norm_le_of_dvd
-- name    : Formalism.InvariantFactorPaths.G7.StarEntryOperators.norm_le_of_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:31.976131+00:00
-- url     : https://prove2.me/theorems/e133a113-c875-4281-a59a-8a924f9e10a2
-- title:
--   Star Entry Operators: norm le of dvd
-- statement:
--   The Star Entry Operators construction uses the norm le of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L196-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L196-L200

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd
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
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact opInt)
open Formalism.GrowthSums (gamP rhoP)
open Formalism.InvariantFactorPaths.G7.StarEntryOperators

theorem Formalism.InvariantFactorPaths.G7.StarEntryOperators.norm_le_of_dvd {K : Type} [NormedField K] [IsUltrametricDist K] {a b : ℕ} (h : a ∣ b) :
    ‖(b : K)‖ ≤ ‖(a : K)‖ := by sorry
