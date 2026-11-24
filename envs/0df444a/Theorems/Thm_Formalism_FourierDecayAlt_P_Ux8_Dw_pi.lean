-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_Dw_pi
-- name    : Formalism.FourierDecayAlt.P.Ux8.Dw_pi
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:37:00.973458+00:00
-- url     : https://prove2.me/theorems/68f4f797-bdc3-4882-ab57-50e39fd19b6a
-- title:
--   Ux8: Dw pi
-- statement:
--   The Ux8 construction uses the Dw pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean#L451-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean#L451-L463

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.Ux8.Dw_pi {w : List (Bool × B.Mat k r)} (hw : ∀ x ∈ w, inLie k r x.2) {F : B.Mat k r → ι → E}
    (hF : B.CkOn w.length (B.GV k r) F) : ∀ g ∈ B.GV k r, ∀ i, Dw w F g i = Dw w (fun g => F g i) g := by sorry
