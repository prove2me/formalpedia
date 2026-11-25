-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_hEmb_inj
-- name    : Formalism.FourierDecayAlt.P.S3x1.hEmb_inj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:26:00.066697+00:00
-- url     : https://prove2.me/theorems/3a1d9001-fac8-5873-8209-19c930b9ff8b
-- title:
--   S3x1: h Emb inj
-- statement:
--   The S3x1 construction uses the h Emb inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean#L151-L154

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x1
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]

theorem Formalism.FourierDecayAlt.P.S3x1.hEmb_inj {h h' : Matrix (Fin k) (Fin k) A} (e : hEmb r h = hEmb r h') : h = h' := by sorry
