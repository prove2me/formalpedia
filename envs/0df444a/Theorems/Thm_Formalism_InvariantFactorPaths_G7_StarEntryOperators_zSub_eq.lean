-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_zSub_eq
-- name    : Formalism.InvariantFactorPaths.G7.StarEntryOperators.zSub_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:42.274538+00:00
-- url     : https://prove2.me/theorems/5750d74e-2cb3-4914-b82d-3d65ac71a267
-- title:
--   Star Entry Operators: z Sub eq
-- statement:
--   The Star Entry Operators construction uses the z Sub eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L68-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L68-L80

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
variable {K : Type} [Field K] {ν r0 r1 : ℕ}

theorem Formalism.InvariantFactorPaths.G7.StarEntryOperators.zSub_eq [NeZero ν] (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K)
    (x : ZV ν r0 r1) :
    zSub TT ξ x = ∑ i, MvPowerSeries.C (Amat TT ξ i x) * MvPowerSeries.X i := by sorry
