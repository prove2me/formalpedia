-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_partial_coboundary
-- name    : Formalism.InvariantFactorPaths.G7.LemTwo.coeff_partial_coboundary
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:57.306492+00:00
-- url     : https://prove2.me/theorems/697daffc-a096-47a6-b0d8-e871f196e3f4
-- title:
--   Lem Two: coeff partial coboundary
-- statement:
--   The Lem Two construction uses the coeff partial coboundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L153-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L153-L163

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemTwo
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.LemTwo.coeff_partial_coboundary {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (G : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (m : ℕ) :
    MvPowerSeries.coeff (ext3 e m) (d1 F G) = MvPowerSeries.coeff e (cob F (sl G m)) := by sorry
