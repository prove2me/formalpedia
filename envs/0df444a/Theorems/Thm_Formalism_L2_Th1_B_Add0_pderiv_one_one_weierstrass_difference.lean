-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Add0_pderiv_one_one_weierstrass_difference
-- name    : Formalism.L2.Th1.B.Add0.pderiv_one_one_weierstrass_difference
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:36.706145+00:00
-- url     : https://prove2.me/theorems/1bb69e65-58a1-4a10-b7d3-cdd1193a6d1b
-- title:
--   Add0: pderiv one one weierstrass difference
-- statement:
--   The Add0 construction uses the pderiv one one weierstrass difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/PderivZeroZeroWeierstrassDifference.lean#L171-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/PderivZeroZeroWeierstrassDifference.lean#L171-L191

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

theorem Formalism.L2.Th1.B.Add0.pderiv_one_one_weierstrass_difference (P : PowerSeries K) : pd 1 (pd 1 (wpDiff P)) =
    -2 + 2 * MvPowerSeries.X 0 ^ 2 * (at1 1 P - at1 0 P) +
      4 * MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 * at1 1 (dz P) +
      MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * at1 1 (dz (dz P)) := by sorry
