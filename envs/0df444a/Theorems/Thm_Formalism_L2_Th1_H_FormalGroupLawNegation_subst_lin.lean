-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_FormalGroupLawNegation_subst_lin
-- name    : Formalism.L2.Th1.H.FormalGroupLawNegation.subst_lin
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:01:27.181668+00:00
-- url     : https://prove2.me/theorems/986d38c2-31f1-4f91-b6b2-cadaa474034d
-- title:
--   Formal Group Law Negation: subst lin
-- statement:
--   The Formal Group Law Negation construction uses the subst lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean#L26-L33

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

theorem Formalism.L2.Th1.H.FormalGroupLawNegation.subst_lin {σ ρ m : Type} [Finite σ] [Fintype m] (c : m → K) (u : m → MvPowerSeries σ K)
    {φ : σ → MvPowerSeries ρ K} (hφ : ∀ s, MvPowerSeries.constantCoeff (φ s) = 0) :
    MvPowerSeries.subst φ (∑ j, MvPowerSeries.C (c j) * u j) =
      ∑ j, MvPowerSeries.C (c j) * MvPowerSeries.subst φ (u j) := by sorry
