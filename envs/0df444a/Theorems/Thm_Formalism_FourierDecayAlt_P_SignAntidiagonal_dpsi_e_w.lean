-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_dpsi_e_w
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.dpsi_e_w
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:34:53.972217+00:00
-- url     : https://prove2.me/theorems/63964adb-478d-4b4c-8317-81b453f3bcf0
-- title:
--   Sign Antidiagonal: dpsi e w
-- statement:
--   The Sign Antidiagonal construction uses the dpsi e w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThirdPeelingMinorMemIdeal.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThirdPeelingMinorMemIdeal.lean#L45-L51

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.dpsi_e_w (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (p : ℕ) (hp : p < r) (w : Fin (k + 1)) :
    dpsiP k r z' (pe k r p) (wI k r w) = if p + 1 = r then z' (wI k r w) else 0 := by sorry
