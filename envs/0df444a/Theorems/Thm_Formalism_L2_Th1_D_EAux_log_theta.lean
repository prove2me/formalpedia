-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_EAux_log_theta
-- name    : Formalism.L2.Th1.D.EAux.log_theta
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:07:25.596338+00:00
-- url     : https://prove2.me/theorems/121a99a8-56b2-5973-8ed0-204e43c831c6
-- title:
--   EAux: log theta
-- statement:
--   The EAux construction uses the log theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/LubinTateLogIsArtinHasse.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/LubinTateLogIsArtinHasse.lean#L49-L55

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_LubinTateLogIsArtinHasse
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

theorem Formalism.L2.Th1.D.EAux.log_theta {l : ℕ} (hl : 2 ≤ l) (g2 g3 ε : K) :
    PowerSeries.subst (thetaS l g2 g3 ε) (logSer (shortW g2 g3)) =
      PowerSeries.C ε * lgF K l := by sorry
