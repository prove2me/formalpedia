-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_MinorFormHomogeneity_coeff_subst_scale
-- name    : Formalism.InvariantFactorPaths.G7.MinorFormHomogeneity.coeff_subst_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:55:58.508506+00:00
-- url     : https://prove2.me/theorems/fd00fcad-c192-4f47-bcc7-364608ab3601
-- title:
--   Minor Form Homogeneity: coeff subst scale
-- statement:
--   The Minor Form Homogeneity construction uses the coeff subst scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EJoint.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EJoint.lean#L17-L26

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_EntryDegree
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
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
open Formalism.InvariantFactorPaths.G7.MinorFormHomogeneity

theorem Formalism.InvariantFactorPaths.G7.MinorFormHomogeneity.coeff_subst_scale {K ι : Type} [Field K] (ϖ : K) (Th : MvPowerSeries ι K) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (MvPowerSeries.subst
      (fun i => MvPowerSeries.C ϖ * (MvPowerSeries.X i : MvPowerSeries ι K)) Th) =
      ϖ ^ n.degree * MvPowerSeries.coeff n Th := by sorry
