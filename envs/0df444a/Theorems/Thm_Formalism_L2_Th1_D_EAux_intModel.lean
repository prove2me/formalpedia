-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_EAux_intModel
-- name    : Formalism.L2.Th1.D.EAux.intModel
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:10:10.317131+00:00
-- url     : https://prove2.me/theorems/fafce077-b7fb-5455-8745-381de7f7e821
-- title:
--   EAux: int Model
-- statement:
--   The EAux construction uses the int Model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/LubinTateLogIsArtinHasse.lean#L209-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/LubinTateLogIsArtinHasse.lean#L209-L219

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

theorem Formalism.L2.Th1.D.EAux.intModel {K : Type} [NormedField K] {g2 g3 : K} (h2 : ‖g2‖ ≤ 1) (h3 : ‖g3‖ ≤ 1)
    (ht : ‖(2 : K)‖ = 1) : IntModel (shortW g2 g3) := by sorry
