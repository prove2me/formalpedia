-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_glev_inv
-- name    : Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.glev_inv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:06:50.143567+00:00
-- url     : https://prove2.me/theorems/4b034afb-f6b9-4d26-abd8-2694fe4fa3ca
-- title:
--   Left Multiplication Rule: glev inv
-- statement:
--   The Left Multiplication Rule construction uses the glev inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/ReflectionColumnDualIsotropic.lean#L155-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/ReflectionColumnDualIsotropic.lean#L155-L161

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

theorem Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.glev_inv {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g⁻¹ ∈ Glev k r i := by sorry
