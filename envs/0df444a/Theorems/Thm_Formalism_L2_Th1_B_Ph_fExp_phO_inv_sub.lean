-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Ph_fExp_phO_inv_sub
-- name    : Formalism.L2.Th1.B.Ph.fExp_phO_inv_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:18.55913+00:00
-- url     : https://prove2.me/theorems/da66014e-b6fc-4b70-8d46-edf40be557ff
-- title:
--   Ph: f Exp ph O inv sub
-- statement:
--   The Ph construction uses the f Exp ph O inv sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/LogSigmaOnePullbackSpec.lean#L187-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/LogSigmaOnePullbackSpec.lean#L187-L222

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Ph
open PowerSeries
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.Ph.fExp_phO_inv_sub (s2 : K) {P l i : PowerSeries K} (hP : ∀ n, Odd n → coeff n P = 0)
    (hl : constantCoeff l = 0) (hl1 : coeff 1 l = 1) (hi : constantCoeff i = 0)
    (hli : subst i l = -l) :
    fExp (subst i (phO s2 P l) - phO s2 P l) = -lU i := by sorry
