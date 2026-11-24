-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_glev_out
-- name    : Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.glev_out
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:06:06.679239+00:00
-- url     : https://prove2.me/theorems/517f4d07-d648-43b8-93ea-5530ff24a5ce
-- title:
--   Left Multiplication Rule: glev out
-- statement:
--   The Left Multiplication Rule construction uses the glev out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/ReflectionColumnDualIsotropic.lean#L163-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/ReflectionColumnDualIsotropic.lean#L163-L185

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

theorem Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.glev_out {l : Fin r} {g : Mx k r} (hg : g ∈ Glev k r l.succ) (p : Fin (2 * r + k + 1))
    (hp : ¬ (l.val < p.val ∧ p.val < 2 * r + k - l.val)) :
    (∀ q, g p q = if p = q then 1 else 0) ∧ (∀ q, g q p = if q = p then 1 else 0) := by sorry
