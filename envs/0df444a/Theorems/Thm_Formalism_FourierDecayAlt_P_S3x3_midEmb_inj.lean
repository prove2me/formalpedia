-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_midEmb_inj
-- name    : Formalism.FourierDecayAlt.P.S3x3.midEmb_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:08:16.709699+00:00
-- url     : https://prove2.me/theorems/f7bfd927-cba5-46a0-b7a6-81df21e2f779
-- title:
--   S3x3: mid Emb inj
-- statement:
--   The S3x3 construction uses the mid Emb inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L206-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L206-L207

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
variable {A : Type} [CommRing A] {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x3.midEmb_inj {a b : Matrix (Fin k) (Fin k) A} (h : midEmb a = midEmb b) : a = b := by sorry
