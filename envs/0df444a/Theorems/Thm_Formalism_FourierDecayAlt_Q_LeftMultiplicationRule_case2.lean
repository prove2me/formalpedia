-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_case2
-- name    : Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.case2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:41:17.845592+00:00
-- url     : https://prove2.me/theorems/928e34e6-ffb3-4fc7-a3a2-9b0331cfd94c
-- title:
--   Left Multiplication Rule: case2
-- statement:
--   The Left Multiplication Rule construction uses the case2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/LeftMultiplicationRule.lean#L204-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/LeftMultiplicationRule.lean#L204-L243

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_LeftMultiplicationRule
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : Fin (2 * r + k + 1) → ℂ}
  {l : Fin r} {D : Set (Mx k r)} {f : Mx k r → E} {c : ℂ} {g₁ : Mx k r}

theorem Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.case2 (hz : inWb k r z) (hL : LeftEq k r z l.castSucc D f) (hc : c ≠ 0)
    (hg₁ : g₁ ∈ Glev k r l.succ) (hgD : w1 k r l c * g₁ ∈ D) (v : Fin (2 * r + k + 1))
    (hv : l.val < v.val ∧ v.val < 2 * r + k - l.val) :
    EH k r (esI k r l) v f (w1 k r l c * g₁) =
      ((star c)⁻¹ * (g₁⁻¹ *ᵥ fvec k r z l.succ) v) • f (w1 k r l c * g₁) := by sorry
