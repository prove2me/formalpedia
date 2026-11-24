-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Ph_phE_inv
-- name    : Formalism.L2.Th1.B.Ph.phE_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:38.595559+00:00
-- url     : https://prove2.me/theorems/60256e23-c1ef-40cd-9888-0037a4db8844
-- title:
--   Ph: ph E inv
-- statement:
--   The Ph construction uses the ph E inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/LogSigmaOnePullbackSpec.lean#L224-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/LogSigmaOnePullbackSpec.lean#L224-L228

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

theorem Formalism.L2.Th1.B.Ph.phE_inv (s2 e1 kap : K) {w l i : PowerSeries K} (hw : ∀ n, Odd n → coeff n w = 0)
    (hl : constantCoeff l = 0) (hi : constantCoeff i = 0) (hli : subst i l = -l) :
    subst i (phE s2 e1 kap w l) = phE s2 e1 kap w l := by sorry
