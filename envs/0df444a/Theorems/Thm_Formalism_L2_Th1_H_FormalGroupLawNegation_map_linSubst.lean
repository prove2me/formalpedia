-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_FormalGroupLawNegation_map_linSubst
-- name    : Formalism.L2.Th1.H.FormalGroupLawNegation.map_linSubst
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:42.458029+00:00
-- url     : https://prove2.me/theorems/80e69362-7b65-4f0c-a5b7-fbb2653daa7a
-- title:
--   Formal Group Law Negation: map lin Subst
-- statement:
--   The Formal Group Law Negation construction uses the map lin Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean#L129-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean#L129-L140

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_SubstSingleVar
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
variable {K₀ K : Type} [Field K₀] [Field K] (ι : K₀ →+* K) {n : Type} [Fintype n]

theorem Formalism.L2.Th1.H.FormalGroupLawNegation.map_linSubst {m : Type} [Finite m] (M : Matrix m n K₀) (T : MvPowerSeries m K₀) :
    MvPowerSeries.map ι (linSubst M T) = linSubst (M.map ι) (MvPowerSeries.map ι T) := by sorry
