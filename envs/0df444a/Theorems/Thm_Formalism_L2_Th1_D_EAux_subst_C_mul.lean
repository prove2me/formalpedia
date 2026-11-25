-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_EAux_subst_C_mul
-- name    : Formalism.L2.Th1.D.EAux.subst_C_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:25:56.501587+00:00
-- url     : https://prove2.me/theorems/78b406b6-abcc-576f-b487-f8354ecea1cc
-- title:
--   EAux: subst C mul
-- statement:
--   The EAux construction uses the subst C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/LubinTateLogIsArtinHasse.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/LubinTateLogIsArtinHasse.lean#L57-L60

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_LubinTateLogIsArtinHasse
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ScaledSeriesSubstitution_subst_C_mul
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_subst_C_mul
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_C_mul

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp BHyp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog BetaHyp)
open Formalism.L2.Th1.A (shortW logSer expSer fgl wpReg iSer xS IntModel)
open Formalism.L2.Th1.B (fLog lU sigS phO)
open Formalism.L2.Th1.D.EAux
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.D.EAux.subst_C_mul {τ : Type} {b : MvPowerSeries τ K} (hb : MvPowerSeries.constantCoeff b = 0)
    (c : K) (f : PowerSeries K) :
    PowerSeries.subst b (PowerSeries.C c * f) = MvPowerSeries.C c * PowerSeries.subst b f := by sorry
