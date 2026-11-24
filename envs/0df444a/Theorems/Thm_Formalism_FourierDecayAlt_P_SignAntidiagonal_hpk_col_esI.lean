-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_hpk_col_esI
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.hpk_col_esI
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:30:58.674343+00:00
-- url     : https://prove2.me/theorems/6a4a4e95-5d6d-4540-885d-82324b5938a4
-- title:
--   Sign Antidiagonal: hpk col es I
-- statement:
--   The Sign Antidiagonal construction uses the hpk col es I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DpsiIsDerivation.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DpsiIsDerivation.lean#L13-L21

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.hpk_col_esI (a : Fin r) (l : Fin (2 * r + k + 1)) :
    Hpk k r l (esI k r a) = if l.val = a.val then 1 else 0 := by sorry
