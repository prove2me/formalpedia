-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_second_capelli_minor_local
-- name    : Formalism.FourierDecayAlt.Q.TPresMain.second_capelli_minor_local
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:53:46.93861+00:00
-- url     : https://prove2.me/theorems/c6359b3b-0ee1-493e-91af-d00e2593945c
-- title:
--   TPres Main: second capelli minor local
-- statement:
--   The TPres Main construction uses the second capelli minor local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/SecondCapelliMinorContinuousLinear.lean#L103-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/SecondCapelliMinorContinuousLinear.lean#L103-L112

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_SecondCapelliMinorContinuousLinear
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

theorem Formalism.FourierDecayAlt.Q.TPresMain.second_capelli_minor_local (hD : IsOpen D) (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ) (f f' : Mx k r → E)
    (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chat2L (EH k r) (posL k r i) u a a' β β' f g = chat2L (EH k r) (posL k r i) u a a' β β' f' g := by sorry
