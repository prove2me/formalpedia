-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_FormalGroupLawNegation_left_side
-- name    : Formalism.L2.Th1.H.FormalGroupLawNegation.left_side
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:43:17.820566+00:00
-- url     : https://prove2.me/theorems/43177193-535d-5472-96e2-c5a6857fa08c
-- title:
--   Formal Group Law Negation: left side
-- statement:
--   The Formal Group Law Negation construction uses the left side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean#L55-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean#L55-L94

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

theorem Formalism.L2.Th1.H.FormalGroupLawNegation.left_side {lg linv : PowerSeries K} (h : IsLogPair lg linv) {O : Type} [Semiring O] (τ : O →+* K)
    (γ : Matrix (Fin 4 × n) (Fin 4 × n) O) (B' : Matrix n n K) (M : Matrix (Fin 4 × n) (Fin 4 × n) K)
    (hM : ∀ (a : Fin 4) (i : n) (w : Fin 4 × n), ∑ j, B' i j * τ (γ (a, j) w) = M (a, i) w)
    (T : MvPowerSeries n K) :
    MvPowerSeries.subst (matCoord lg linv τ γ)
        (tensor4 (MvPowerSeries.subst (fun i => ∑ j, MvPowerSeries.C (B' i j) * at1 j lg) T)) =
      MvPowerSeries.subst (fun w => at1 w lg) (linSubst M (tensor4 T)) := by sorry
