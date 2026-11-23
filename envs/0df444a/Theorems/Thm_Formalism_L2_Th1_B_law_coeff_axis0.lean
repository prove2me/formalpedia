-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_law_coeff_axis0
-- name    : Formalism.L2.Th1.B.law_coeff_axis0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:17.659805+00:00
-- url     : https://prove2.me/theorems/454e2f2a-aad8-4b30-9238-9d15b8b323c9
-- title:
--   B: law coeff axis0
-- statement:
--   The B construction uses the law coeff axis0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffSeriesAtVariable.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffSeriesAtVariable.lean#L51-L60

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_IntegralInverse
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G.LogP (hs2 subst2_subst psubst_subst psubst_injective)
variable {K : Type} [Field K] {ι : Type}

theorem Formalism.L2.Th1.B.law_coeff_axis0 (H : MvPowerSeries (Fin 2) K) (n : Fin 2 →₀ ℕ) (hn : n 1 = 0) :
    MvPowerSeries.coeff n H = MvPowerSeries.coeff n
      (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] H) := by sorry
