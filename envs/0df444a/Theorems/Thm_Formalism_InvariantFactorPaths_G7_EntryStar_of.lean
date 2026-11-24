-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_EntryStar_of
-- name    : Formalism.InvariantFactorPaths.G7.EntryStar_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:02.639489+00:00
-- url     : https://prove2.me/theorems/ac9644ca-992c-4096-a9dc-3d9cbf21cbbf
-- title:
--   G7: Entry Star of
-- statement:
--   The G7 construction uses the Entry Star of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L309-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L309-L403

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46

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

theorem Formalism.InvariantFactorPaths.G7.EntryStar_of (hT : TermBound) (hH : HhDecomp) (hC : ClassSubst)
    (hJ : Formalism.DworkPowerSeriesWeights.JetPairLin.{0}) (hS : StarArith) (hD : HasseDegree) (hM : MinorProdDegree) :
    EntryStar := by sorry
