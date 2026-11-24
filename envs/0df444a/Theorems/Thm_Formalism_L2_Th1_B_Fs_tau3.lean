-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Fs_tau3
-- name    : Formalism.L2.Th1.B.Fs.tau3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:59:07.483482+00:00
-- url     : https://prove2.me/theorems/847f14a2-9e87-44a7-a6b1-5639c0fe2ed4
-- title:
--   Fs: tau3
-- statement:
--   The Fs construction uses the tau3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L108-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L108-L116

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Fs
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K

theorem Formalism.L2.Th1.B.Fs.tau3 (hT : TauRule) {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) {j k : Fin 3}
    (hjk : j ≠ k) :
    (MvPowerSeries.X j - MvPowerSeries.X k) * (pd j (wp3 P j k) - pd k (wp3 P j k)) =
      wp3 P j k * (2 + 2 * (MvPowerSeries.X j - MvPowerSeries.X k) *
        (evalDiffThree j k (dz (sigS P)) - at1 j (dz (sigS P)) + at1 k (dz (sigS P)))) := by sorry
