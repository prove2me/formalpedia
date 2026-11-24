-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_qminor_eq
-- name    : Formalism.FourierDecayAlt.Q.TPresMain.qminor_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:24:53.97801+00:00
-- url     : https://prove2.me/theorems/f117d0c2-ecb5-4451-ba27-41025c846f53
-- title:
--   TPres Main: qminor eq
-- statement:
--   The TPres Main construction uses the qminor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/ExpSecondHermitianMemLevel.lean#L245-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/ExpSecondHermitianMemLevel.lean#L245-L249

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

theorem Formalism.FourierDecayAlt.Q.TPresMain.qminor_eq {t : ℕ} (α β : Fin t → Fin (mdim k r i)) (u : ℂ) (f : Mx k r → E) :
    qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u f =
      ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ) •
        foldP k r i (List.ofFn fun m : Fin t => (u - ((m : ℕ) : ℂ), α (σ m), β m)) f) := by sorry
