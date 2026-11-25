-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_FormalGroupLawNegation_subst_single_var
-- name    : Formalism.L2.Th1.H.FormalGroupLawNegation.subst_single_var
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:49:57.634002+00:00
-- url     : https://prove2.me/theorems/15dda93b-37fb-42c9-88b1-d84fc559bb96
-- title:
--   Formal Group Law Negation: subst single var
-- statement:
--   The Formal Group Law Negation construction uses the subst single var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean#L48-L53

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_SubstSingleVar
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_single_var
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

theorem Formalism.L2.Th1.H.FormalGroupLawNegation.subst_single_var {σ ρ : Type} [Finite σ] (s : σ) (f : PowerSeries K) {φ : σ → MvPowerSeries ρ K}
    (hφ : ∀ s, MvPowerSeries.constantCoeff (φ s) = 0) :
    MvPowerSeries.subst φ (at1 s f) = PowerSeries.subst (φ s) f := by sorry
