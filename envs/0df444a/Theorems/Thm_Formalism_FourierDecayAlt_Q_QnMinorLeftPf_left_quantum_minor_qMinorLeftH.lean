-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QnMinorLeftPf_left_quantum_minor_qMinorLeftH
-- name    : Formalism.FourierDecayAlt.Q.QnMinorLeftPf.left_quantum_minor_qMinorLeftH
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:37:22.690797+00:00
-- url     : https://prove2.me/theorems/60b5ac0e-7971-46da-9339-d791cc63bf5c
-- title:
--   Qn Minor Left Pf: left quantum minor q Minor Left H
-- statement:
--   The Qn Minor Left Pf construction uses the left quantum minor q Minor Left H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftQuantumMinor/QuantumMinorLeftHermitian.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftQuantumMinor/QuantumMinorLeftHermitian.lean#L13-L27

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftQuantumMinor_QuantumMinorLeftHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QnMinorLeftPf
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.Q.QnMinorLeftPf.left_quantum_minor_qMinorLeftH : QMinorLeftH := by sorry
