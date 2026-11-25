-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_Tm_Emir
-- name    : Formalism.FourierDecayAlt.P.PBG.Tm_Emir
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:03:26.465656+00:00
-- url     : https://prove2.me/theorems/d5e9858e-04bd-45f6-ac89-963a799dffb3
-- title:
--   PBG: Tm Emir
-- statement:
--   The PBG construction uses the Tm Emir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L238-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L238-L244

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

theorem Formalism.FourierDecayAlt.P.PBG.Tm_Emir (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (v : ℂ) (p q : Fin (2 * r + k + 1)) :
    Tm (Emir E) v p q = (ep p * ep q) • Tm (Formalism.FourierDecayAlt.P.Qx5.Eop E) v (rv p) (rv q) := by sorry
