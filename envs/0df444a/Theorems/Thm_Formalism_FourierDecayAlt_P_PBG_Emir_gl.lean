-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_Emir_gl
-- name    : Formalism.FourierDecayAlt.P.PBG.Emir_gl
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:02:41.650239+00:00
-- url     : https://prove2.me/theorems/29f92e9f-230d-5346-ba6f-a83361893ae9
-- title:
--   PBG: Emir gl
-- statement:
--   The PBG construction uses the Emir gl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L202-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L202-L236

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHeadV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.PBG.Emir_gl {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} (hE : Formalism.REAL.GlRel E) :
    Formalism.REAL.GlRel (Emir E) := by sorry
