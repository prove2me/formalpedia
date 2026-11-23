-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_DeterminantJetScaling_deg_eq
-- name    : Formalism.InvariantFactorPaths.G7.DeterminantJetScaling.deg_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:48.327474+00:00
-- url     : https://prove2.me/theorems/5d9a7ee6-7514-4620-900c-0cdb283530d0
-- title:
--   Determinant Jet Scaling: deg eq
-- statement:
--   The Determinant Jet Scaling construction uses the deg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EKernel.lean#L76-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EKernel.lean#L76-L84

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EKernel
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
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPairPoly minorProd mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.DeterminantJetScaling

theorem Formalism.InvariantFactorPaths.G7.DeterminantJetScaling.deg_eq {ν : ℕ} [NeZero ν] (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) :
    ∑ s, ((alG TT colN hts s : ℝ) + lsG TT colN hts s) = ((∑ s, ∑ c, hts s c : ℕ) : ℝ) := by sorry
