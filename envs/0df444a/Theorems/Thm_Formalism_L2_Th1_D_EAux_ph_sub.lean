-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_EAux_ph_sub
-- name    : Formalism.L2.Th1.D.EAux.ph_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:22:58.487808+00:00
-- url     : https://prove2.me/theorems/4652a69f-bd70-5f80-b3d1-875d6ed9222a
-- title:
--   EAux: ph sub
-- statement:
--   The EAux construction uses the ph sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/LubinTateLogIsArtinHasse.lean#L106-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/LubinTateLogIsArtinHasse.lean#L106-L167

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
open EAux
open Formalism.L2.Th1.D.EAux

theorem Formalism.L2.Th1.D.EAux.ph_sub {K : Type} [Field K] [CharZero K] {l : ℕ} (hl : 2 ≤ l) (g2 g3 s2 : K) {ε : K}
    (hε : ε ≠ 0) :
    PowerSeries.constantCoeff (PowerSeries.C ε⁻¹ * lU (thetaS l g2 g3 ε)) = 1 ∧
    phFF l g2 g3 s2 ε - PowerSeries.subst (thetaS l g2 g3 ε) (phCurve g2 g3 s2) =
      -fLog (PowerSeries.C ε⁻¹ * lU (thetaS l g2 g3 ε)) := by sorry
