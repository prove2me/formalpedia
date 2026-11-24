-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_DeterminantJetScaling_minorProd_hom
-- name    : Formalism.InvariantFactorPaths.G7.DeterminantJetScaling.minorProd_hom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:55.271831+00:00
-- url     : https://prove2.me/theorems/af1920ff-8f2c-47ff-8bf1-dc846a87698e
-- title:
--   Determinant Jet Scaling: minor Prod hom
-- statement:
--   The Determinant Jet Scaling construction uses the minor Prod hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EKernel.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EKernel.lean#L30-L38

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

theorem Formalism.InvariantFactorPaths.G7.DeterminantJetScaling.minorProd_hom {R σ : Type} [CommRing R] {N0 N1 C : ℕ}
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (hrow : ∀ i b, (row i b).IsHomogeneous 1)
    (q : Fin C → ℕ) (hq : ∀ c, q c ≤ N0) (I : ∀ c, Fin (q c) → Fin N1) :
    (minorProd row q hq I).IsHomogeneous (∑ c, q c) := by sorry
