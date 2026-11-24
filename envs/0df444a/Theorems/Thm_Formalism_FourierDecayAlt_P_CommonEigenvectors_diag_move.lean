-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CommonEigenvectors_diag_move
-- name    : Formalism.FourierDecayAlt.P.CommonEigenvectors.diag_move
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:53:18.386081+00:00
-- url     : https://prove2.me/theorems/fecb01b2-9c2a-4e35-aae9-55d85ba50aad
-- title:
--   Common Eigenvectors: diag move
-- statement:
--   The Common Eigenvectors construction uses the diag move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommonEigenvectors.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommonEigenvectors.lean#L58-L65

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CommonEigenvectors
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.P.CommonEigenvectors.diag_move {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (c a b : Fin n) (x : V) :
    E c c (E a b x) = E a b (E c c x) + ((if c = a then E a b x else 0) - (if b = c then E a b x else 0)) := by sorry
