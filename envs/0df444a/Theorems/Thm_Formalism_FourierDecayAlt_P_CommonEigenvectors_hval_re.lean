-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CommonEigenvectors_hval_re
-- name    : Formalism.FourierDecayAlt.P.CommonEigenvectors.hval_re
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:54:02.026666+00:00
-- url     : https://prove2.me/theorems/11d0cacd-d42b-493d-ba4b-306e2b1c97ea
-- title:
--   Common Eigenvectors: hval re
-- statement:
--   The Common Eigenvectors construction uses the hval re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommonEigenvectors.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommonEigenvectors.lean#L85-L89

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

theorem Formalism.FourierDecayAlt.P.CommonEigenvectors.hval_re {n : ℕ} (θ : Fin n → ℂ) :
    (∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) * θ c).re = hval θ := by sorry
