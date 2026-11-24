-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Jets_invariant_derivation_subst_law_pair
-- name    : Formalism.L2.Th1.B.Jets.invariant_derivation_subst_law_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:43.2678+00:00
-- url     : https://prove2.me/theorems/4e164396-a797-4ec8-bb93-e1250df97cdd
-- title:
--   Jets: invariant derivation subst law pair
-- statement:
--   The Jets construction uses the invariant derivation subst law pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/InvariantDerivationSubstLawThree.lean#L142-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/InvariantDerivationSubstLawThree.lean#L142-L161

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Jets
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3)
open Formalism.G.LogP (hs2 psubst_subst constantCoeff_subst_of_zero psubst_injective)
variable {K : Type} [Field K] [CharZero K]
variable {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K}

theorem Formalism.L2.Th1.B.Jets.invariant_derivation_subst_law_pair (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (j a b : Fin 3) (hab : a ≠ b) (g : PowerSeries K) :
    Dj l j (PowerSeries.subst (U2 F a b) g) =
      if a = j ∨ b = j then PowerSeries.subst (U2 F a b) (Dinv l g) else 0 := by sorry
