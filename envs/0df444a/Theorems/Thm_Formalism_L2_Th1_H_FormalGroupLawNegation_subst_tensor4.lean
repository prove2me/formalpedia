-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_FormalGroupLawNegation_subst_tensor4
-- name    : Formalism.L2.Th1.H.FormalGroupLawNegation.subst_tensor4
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:28:52.27634+00:00
-- url     : https://prove2.me/theorems/c8b4a5d3-5de5-5589-a8f0-2ac675199d00
-- title:
--   Formal Group Law Negation: subst tensor4
-- statement:
--   The Formal Group Law Negation construction uses the subst tensor4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean#L35-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean#L35-L46

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_SubstSingleVar
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.C (IsLogPair)
open Formalism.L2.Th1.E (tensor4 matCoord thetaProd)
open Formalism.L2.Th1.H.FormalGroupLawNegation
variable {K : Type} [Field K] {n : Type} [Fintype n]

theorem Formalism.L2.Th1.H.FormalGroupLawNegation.subst_tensor4 {ρ : Type} (T : MvPowerSeries n K) {φ : Fin 4 × n → MvPowerSeries ρ K}
    (hφ : ∀ s, MvPowerSeries.constantCoeff (φ s) = 0) :
    MvPowerSeries.subst φ (tensor4 T) = ∏ a : Fin 4, MvPowerSeries.subst (fun i => φ (a, i)) T := by sorry
