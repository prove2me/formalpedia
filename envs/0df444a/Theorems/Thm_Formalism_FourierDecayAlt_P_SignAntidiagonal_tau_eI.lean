-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_tau_eI
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.tau_eI
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:30:56.100433+00:00
-- url     : https://prove2.me/theorems/f488b3b0-475e-401e-b54a-8c808d2e4f5b
-- title:
--   Sign Antidiagonal: tau e I
-- statement:
--   The Sign Antidiagonal construction uses the tau e I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L46-L48

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneAddProjectionMemIsotropicSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianInsertionVectorOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_tau_eI

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
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants
noncomputable section
variable {k : ℕ}
variable (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.tau_eI (c : Fin (m + 1)) : WeylGroupFacts.tau k (m + 1) (eI k (m + 1) c) = esI k (m + 1) c := by sorry
