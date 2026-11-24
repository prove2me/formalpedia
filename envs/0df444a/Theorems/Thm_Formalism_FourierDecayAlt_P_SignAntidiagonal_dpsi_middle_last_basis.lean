-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_dpsi_middle_last_basis
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.dpsi_middle_last_basis
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:34:42.229007+00:00
-- url     : https://prove2.me/theorems/b1076834-d772-4073-b6d3-f4e00a42e059
-- title:
--   Sign Antidiagonal: dpsi middle last basis
-- statement:
--   The Sign Antidiagonal construction uses the dpsi middle last basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThirdPeelingMinorMemIdeal.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThirdPeelingMinorMemIdeal.lean#L53-L59

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.dpsi_middle_last_basis (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (l : ℕ) (hl : l < r) (w : Fin (k + 1)) :
    dpsiP k r z' (wI k r w) (ps k r l) = if l + 1 = r then herm (Hpk k r) (bvec (wI k r w)) z' else 0 := by sorry
