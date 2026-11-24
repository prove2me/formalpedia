-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Ph_phO_inv_sub
-- name    : Formalism.L2.Th1.B.Ph.phO_inv_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:36.720408+00:00
-- url     : https://prove2.me/theorems/cebf93d5-edb9-4395-bef2-af3184481249
-- title:
--   Ph: ph O inv sub
-- statement:
--   The Ph construction uses the ph O inv sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/LogSigmaOnePullbackSpec.lean#L174-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/LogSigmaOnePullbackSpec.lean#L174-L185

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

theorem Formalism.L2.Th1.B.Ph.phO_inv_sub (s2 : K) {P l i : PowerSeries K} (hP : ∀ n, Odd n → coeff n P = 0)
    (hl : constantCoeff l = 0) (hl1 : coeff 1 l = 1) (hi : constantCoeff i = 0)
    (hli : subst i l = -l) :
    subst i (phO s2 P l) - phO s2 P l = fLog (lU l) - fLog (subst i (lU l)) := by sorry
