-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_subst_slice
-- name    : Formalism.InvariantFactorPaths.G7.LemTwo.coeff_subst_slice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:06.130192+00:00
-- url     : https://prove2.me/theorems/d682b287-dafc-45df-b7f8-238bdb00db1e
-- title:
--   Lem Two: coeff subst slice
-- statement:
--   The Lem Two construction uses the coeff subst slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L107-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L107-L151

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

theorem Formalism.InvariantFactorPaths.G7.LemTwo.coeff_subst_slice {f : MvPowerSeries (Fin 2) K} (hf : MvPowerSeries.constantCoeff f = 0)
    (G : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (m : ℕ) :
    MvPowerSeries.coeff (ext3 e m) (MvPowerSeries.subst ![in3 f, MvPowerSeries.X 2] G) =
      MvPowerSeries.coeff e (PowerSeries.subst f (sl G m)) := by sorry
