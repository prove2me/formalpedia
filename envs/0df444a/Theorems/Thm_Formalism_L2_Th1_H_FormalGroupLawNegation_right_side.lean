-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_FormalGroupLawNegation_right_side
-- name    : Formalism.L2.Th1.H.FormalGroupLawNegation.right_side
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:58:31.463956+00:00
-- url     : https://prove2.me/theorems/aefe710a-b319-5b82-b8e9-3fb8d6463af7
-- title:
--   Formal Group Law Negation: right side
-- statement:
--   The Formal Group Law Negation construction uses the right side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean#L96-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean#L96-L110

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

theorem Formalism.L2.Th1.H.FormalGroupLawNegation.right_side {lg : PowerSeries K} (hlg : PowerSeries.constantCoeff lg = 0) {m κ : Type} [Fintype m]
    (S : Finset κ) (r : κ → K) (f : κ → m → PowerSeries K) :
    MvPowerSeries.subst (fun w => at1 w lg) (∑ x ∈ S, MvPowerSeries.C (r x) * ∏ w, at1 w (f x w)) =
      ∑ x ∈ S, MvPowerSeries.C (r x) * ∏ w, at1 w ((f x w).subst lg) := by sorry
