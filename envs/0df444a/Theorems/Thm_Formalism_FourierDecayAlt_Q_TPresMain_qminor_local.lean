-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_qminor_local
-- name    : Formalism.FourierDecayAlt.Q.TPresMain.qminor_local
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:25:05.965799+00:00
-- url     : https://prove2.me/theorems/0d1d6666-3544-466c-bf40-20ab369b7456
-- title:
--   TPres Main: qminor local
-- statement:
--   The TPres Main construction uses the qminor local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/ExpSecondHermitianMemLevel.lean#L257-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/ExpSecondHermitianMemLevel.lean#L257-L264

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

theorem Formalism.FourierDecayAlt.Q.TPresMain.qminor_local (hD : IsOpen D) {t : ℕ} (α β : Fin t → Fin (mdim k r i)) (u : ℂ)
    (f f' : Mx k r → E) (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u f g =
      qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u f' g := by sorry
