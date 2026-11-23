-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Add0_pderiv_one_weierstrass_difference
-- name    : Formalism.L2.Th1.B.Add0.pderiv_one_weierstrass_difference
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:48.040678+00:00
-- url     : https://prove2.me/theorems/c16adf5e-9184-427e-b2b6-a7e745ade6ed
-- title:
--   Add0: pderiv one weierstrass difference
-- statement:
--   The Add0 construction uses the pderiv one weierstrass difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/PderivZeroZeroWeierstrassDifference.lean#L128-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/PderivZeroZeroWeierstrassDifference.lean#L128-L147

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
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
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.B.Add0
variable {K : Type} [Field K] [CharZero K]
local notation "A2" => MvPowerSeries (Fin 2) K

theorem Formalism.L2.Th1.B.Add0.pderiv_one_weierstrass_difference (P : PowerSeries K) : pd 1 (wpDiff P) =
    -2 * MvPowerSeries.X 1 + 2 * MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 * (at1 1 P - at1 0 P) +
      MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * at1 1 (dz P) := by sorry
