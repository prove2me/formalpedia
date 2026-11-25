-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_fsum
-- name    : Formalism.FourierDecayAlt.P.JFxE.ev_fsum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:30:09.492407+00:00
-- url     : https://prove2.me/theorems/53724935-f0f4-405b-8465-282e6779a97f
-- title:
--   JFx E: ev fsum
-- statement:
--   The JFx E construction uses the ev fsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RepIntCastMul.lean#L297-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RepIntCastMul.lean#L297-L301

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

theorem Formalism.FourierDecayAlt.P.JFxE.ev_fsum {ι : Type*} (s : Finset ι) (F : ι → AA k r E) (f : Mat k r → E) (x : Mat k r) :
    ev Eop (∑ i ∈ s, F i) f x = ∑ i ∈ s, ev Eop (F i) f x := by sorry
