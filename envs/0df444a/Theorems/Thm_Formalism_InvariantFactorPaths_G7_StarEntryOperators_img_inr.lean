-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_img_inr
-- name    : Formalism.InvariantFactorPaths.G7.StarEntryOperators.img_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:08.344683+00:00
-- url     : https://prove2.me/theorems/de711336-c780-4f72-892e-ce20919601f6
-- title:
--   Star Entry Operators: img inr
-- statement:
--   The Star Entry Operators construction uses the img inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L82-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L82-L90

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

theorem Formalism.InvariantFactorPaths.G7.StarEntryOperators.img_inr [NeZero ν] (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K)
    (y : ZV ν r0 r1) :
    (∑ x, MvPolynomial.C (Amat TT ξ (Sum.inr y) x) * MvPolynomial.X x :
      MvPolynomial (ZV ν r0 r1) K) = MvPolynomial.X y := by sorry
