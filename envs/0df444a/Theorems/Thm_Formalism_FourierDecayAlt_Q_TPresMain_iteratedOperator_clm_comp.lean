-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_iteratedOperator_clm_comp
-- name    : Formalism.FourierDecayAlt.Q.TPresMain.iteratedOperator_clm_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:53:59.858991+00:00
-- url     : https://prove2.me/theorems/5277f944-2f63-42af-b36f-8ce2c8130cf7
-- title:
--   TPres Main: iterated Operator clm comp
-- statement:
--   The TPres Main construction uses the iterated Operator clm comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/ExpSecondHermitianMemLevel.lean#L235-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/ExpSecondHermitianMemLevel.lean#L235-L243

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

theorem Formalism.FourierDecayAlt.Q.TPresMain.iteratedOperator_clm_comp (hD : IsOpen D) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    ∀ g ∈ Glev k r i ∩ D, foldP k r i l (fun y => L (f y)) g = L (foldP k r i l f g) := by sorry
