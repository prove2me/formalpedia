-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_rep_sum
-- name    : Formalism.FourierDecayAlt.Q.TInvW.rep_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:44:26.374574+00:00
-- url     : https://prove2.me/theorems/e7863e0b-8664-43d3-9610-421ed68450d8
-- title:
--   TInv W: rep sum
-- statement:
--   The TInv W construction uses the rep sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L182-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L182-L187

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem Formalism.FourierDecayAlt.Q.TInvW.rep_sum {ι : Type*} [Fintype ι] (c : ι → ℂ) {F : ι → Mx k r → E}
    {x : ι → Sm E k r i D} (h : ∀ j, Rep (F j) (x j).1) :
    Rep (fun g => ∑ j, c j • F j g) (∑ j, c j • x j).1 := by sorry
