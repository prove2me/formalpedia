-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_Dx_pi
-- name    : Formalism.FourierDecayAlt.P.Ux8.Dx_pi
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:37:16.258313+00:00
-- url     : https://prove2.me/theorems/79f02340-9d45-4cb9-ab3a-929ff2ad6c60
-- title:
--   Ux8: Dx pi
-- statement:
--   The Ux8 construction uses the Dx pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean#L444-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean#L444-L449

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

theorem Formalism.FourierDecayAlt.P.Ux8.Dx_pi {x : Bool × B.Mat k r} (hx : inLie k r x.2) {F : B.Mat k r → ι → E} (hF : B.CkOn 1 (B.GV k r) F)
    (g : B.Mat k r) (hg : g ∈ B.GV k r) (i : ι) : Dx x F g i = Dx x (fun g => F g i) g := by sorry
