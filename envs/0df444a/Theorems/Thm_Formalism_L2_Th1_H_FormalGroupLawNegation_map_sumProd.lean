-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_FormalGroupLawNegation_map_sumProd
-- name    : Formalism.L2.Th1.H.FormalGroupLawNegation.map_sumProd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:52:15.935724+00:00
-- url     : https://prove2.me/theorems/cbf10e30-3b52-4469-9a3e-e0280a0159ac
-- title:
--   Formal Group Law Negation: map sum Prod
-- statement:
--   The Formal Group Law Negation construction uses the map sum Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean#L142-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean#L142-L150

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

theorem Formalism.L2.Th1.H.FormalGroupLawNegation.map_sumProd {κ : Type} (S : Finset κ) (r : κ → K₀) (f : κ → n → PowerSeries K₀) :
    MvPowerSeries.map ι (∑ x ∈ S, MvPowerSeries.C (r x) * ∏ w, at1 w (f x w)) =
      ∑ x ∈ S, MvPowerSeries.C (ι (r x)) * ∏ w, at1 w (PowerSeries.map ι (f x w)) := by sorry
