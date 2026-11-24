-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_dpsi_is_derivation
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.dpsi_is_derivation
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:19:53.421858+00:00
-- url     : https://prove2.me/theorems/6d10675f-d8aa-40e5-b24a-86e9bd81f95a
-- title:
--   Sign Antidiagonal: dpsi is derivation
-- statement:
--   The Sign Antidiagonal construction uses the dpsi is derivation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DpsiIsDerivation.lean#L99-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DpsiIsDerivation.lean#L99-L231

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.dpsi_is_derivation : DpsiDerivation := by sorry
