-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_hEmb_mul
-- name    : Formalism.FourierDecayAlt.P.S3x3.hEmb_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:34.533736+00:00
-- url     : https://prove2.me/theorems/6482b13b-1971-4f73-a9f7-48cccee8d4be
-- title:
--   S3x3: h Emb mul
-- statement:
--   The S3x3 construction uses the h Emb mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L209-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L209-L210

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

theorem Formalism.FourierDecayAlt.P.S3x3.hEmb_mul (a b : Matrix (Fin k) (Fin k) A) : hEmb r (a * b) = hEmb r a * hEmb r b := by sorry
