-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_herm_bvec_sum
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:13:21.87982+00:00
-- url     : https://prove2.me/theorems/7f5481c6-55b5-4a18-a15c-839fa0f501a6
-- title:
--   Sign Antidiagonal: herm bvec sum
-- statement:
--   The Sign Antidiagonal construction uses the herm bvec sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictMonoSnoc.lean#L82-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictMonoSnoc.lean#L82-L116

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictMonoSnoc
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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_sum (k r : ℕ) (yb : Fin (2 * r + k + 1) → ℂ) (hyb : inWb k r yb) (p : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec p) yb =
      ∑ w : Fin (k + 1), herm (Hpk k r) (bvec (wI k r w)) yb * (if p = wI k r w then 1 else 0) := by sorry
