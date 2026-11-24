-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_reflection_column_dual_isotropic
-- name    : Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.reflection_column_dual_isotropic
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:05:14.636017+00:00
-- url     : https://prove2.me/theorems/10ecb607-62d3-4297-a5f3-10f36c9a5a51
-- title:
--   Left Multiplication Rule: reflection column dual isotropic
-- statement:
--   The Left Multiplication Rule construction uses the reflection column dual isotropic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/ReflectionColumnDualIsotropic.lean#L61-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/ReflectionColumnDualIsotropic.lean#L61-L69

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.reflection_column_dual_isotropic (l : Fin r) (c : ℂ) (p : Fin (2 * r + k + 1)) :
    w1 k r l c p (esI k r l) = if p = eI k r l then (star c)⁻¹ else 0 := by sorry
