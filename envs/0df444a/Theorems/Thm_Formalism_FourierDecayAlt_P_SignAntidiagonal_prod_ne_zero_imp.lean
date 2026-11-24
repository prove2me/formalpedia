-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_prod_ne_zero_imp
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.prod_ne_zero_imp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:53.017352+00:00
-- url     : https://prove2.me/theorems/ea2cc546-8064-4588-91c9-86f929397fc0
-- title:
--   Sign Antidiagonal: prod ne zero imp
-- statement:
--   The Sign Antidiagonal construction uses the prod ne zero imp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeadingTermIdentity.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeadingTermIdentity.lean#L37-L41

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlMonoConst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.prod_ne_zero_imp {m N : ℕ} (a b : Fin m → Fin N) (σ : Equiv.Perm (Fin m))
    (h : ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0) ≠ 0) : ∀ k, a (σ k) = b k := by sorry
