-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_hEmb_map
-- name    : Formalism.FourierDecayAlt.P.S3x3.hEmb_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:54:03.989565+00:00
-- url     : https://prove2.me/theorems/d3cb94cc-4f9e-4615-b5af-55643f353324
-- title:
--   S3x3: h Emb map
-- statement:
--   The S3x3 construction uses the h Emb map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L218-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L218-L220

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

theorem Formalism.FourierDecayAlt.P.S3x3.hEmb_map {B : Type} [CommRing B] (f : A →+* B) (h : Matrix (Fin k) (Fin k) A) :
    (hEmb r h).map f = hEmb r (h.map f) := by sorry
