-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_ell_S
-- name    : Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.ell_S
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:43:57.181137+00:00
-- url     : https://prove2.me/theorems/fb64e151-2dcb-46ed-8e76-955f58778f05
-- title:
--   Left Multiplication Rule: ell S
-- statement:
--   The Left Multiplication Rule construction uses the ell S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/MulApplyS.lean#L146-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/MulApplyS.lean#L146-L178

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.ell_S {l : Fin r} {M : Mx k r} (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (hM : InS k r l M) : ell k r z M = (M *ᵥ fvec k r z l.succ) (eI k r l) := by sorry
