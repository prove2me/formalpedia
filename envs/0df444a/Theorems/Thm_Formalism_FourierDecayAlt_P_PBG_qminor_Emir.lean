-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_qminor_Emir
-- name    : Formalism.FourierDecayAlt.P.PBG.qminor_Emir
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:04:20.875026+00:00
-- url     : https://prove2.me/theorems/b7891a8e-ba00-450d-a3b0-f5112fae4835
-- title:
--   PBG: qminor Emir
-- statement:
--   The PBG construction uses the qminor Emir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L253-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L253-L262

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

theorem Formalism.FourierDecayAlt.P.PBG.qminor_Emir (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1))
    (u : ℂ) : qminor (Emir E) a b u =
      ((∏ i, ep (a i)) * (∏ i, ep (b i))) • qminor (Formalism.FourierDecayAlt.P.Qx5.Eop E) (rv ∘ a) (rv ∘ b) u := by sorry
