-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_iteratedOperator_cons
-- name    : Formalism.FourierDecayAlt.Q.TPresMain.iteratedOperator_cons
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:24:47.832382+00:00
-- url     : https://prove2.me/theorems/57284e19-ce2f-479e-b736-16319b1e9f41
-- title:
--   TPres Main: iterated Operator cons
-- statement:
--   The TPres Main construction uses the iterated Operator cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/ExpSecondHermitianMemLevel.lean#L215-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/ExpSecondHermitianMemLevel.lean#L215-L217

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem Formalism.FourierDecayAlt.Q.TPresMain.iteratedOperator_cons (x : ℂ × Fin (mdim k r i) × Fin (mdim k r i)) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    (f : Mx k r → E) :
    foldP k r i (x :: l) f = Top (EH k r) x.1 (posL k r i x.2.1) (posL k r i x.2.2) (foldP k r i l f) := by sorry
