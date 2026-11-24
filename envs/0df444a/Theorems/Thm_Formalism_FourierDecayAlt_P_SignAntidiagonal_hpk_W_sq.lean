-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_hpk_W_sq
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.hpk_W_sq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:20:39.79066+00:00
-- url     : https://prove2.me/theorems/b47710d9-28eb-4ab2-b5aa-ed572014a092
-- title:
--   Sign Antidiagonal: hpk W sq
-- statement:
--   The Sign Antidiagonal construction uses the hpk W sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DpsiIsDerivation.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DpsiIsDerivation.lean#L43-L46

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.hpk_W_sq (w : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) : Hpk k r w w * Hpk k r w w = 1 := by sorry
