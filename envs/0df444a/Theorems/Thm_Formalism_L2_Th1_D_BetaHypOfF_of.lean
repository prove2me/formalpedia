-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_BetaHypOfF_of
-- name    : Formalism.L2.Th1.D.BetaHypOfF_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:28.460803+00:00
-- url     : https://prove2.me/theorems/a4f06eeb-f784-4019-9aaf-99b20339af97
-- title:
--   D: Beta Hyp Of F of
-- statement:
--   The D construction uses the Beta Hyp Of F of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ExponentialSpecification.lean#L199-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ExponentialSpecification.lean#L199-L219

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExponentialSpecification
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_coeff_one_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_constantCoeff_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_funEq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_subst_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_rescale_lgF

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws (constantCoeff_lgF coeff_one_lgF lgF_subst_inj lgF_funEq map_lgF
  rescale_lgF)
open FormalExponential

theorem Formalism.L2.Th1.D.BetaHypOfF_of : TeichSigma → BetaHypOfF := by sorry
