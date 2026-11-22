-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_card_GL_subtype
-- name    : Formalism.FourierDecayAlt.P.S3x3.card_GL_subtype
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:39.931603+00:00
-- url     : https://prove2.me/theorems/a24cc9d5-de4e-477d-8124-64f5f8f3f253
-- title:
--   S3x3: card GL subtype
-- statement:
--   The S3x3 construction uses the card GL subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L449-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L449-L456

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x3
open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)

theorem Formalism.FourierDecayAlt.P.S3x3.card_GL_subtype {ι K : Type} [Fintype ι] [DecidableEq ι] [CommRing K]
    (P : Matrix ι ι K → Prop) (hP : ∀ x, P x → IsUnit x.det) :
    Nat.card {g : GL ι K // P g} = Nat.card {x : Matrix ι ι K // P x} := by sorry
