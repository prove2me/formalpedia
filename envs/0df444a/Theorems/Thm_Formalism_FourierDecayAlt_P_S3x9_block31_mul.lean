-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x9_block31_mul
-- name    : Formalism.FourierDecayAlt.P.S3x9.block31_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:16:07.353871+00:00
-- url     : https://prove2.me/theorems/65a3b2ef-9a02-47c6-9248-2ad4472851db
-- title:
--   S3x9: block31 mul
-- statement:
--   The S3x9 construction uses the block31 mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block32EqZeroOfUnipotent.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block32EqZeroOfUnipotent.lean#L31-L34

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Minors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block32EqZeroOfUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x9
open Matrix Finset
open Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni upUniG)

theorem Formalism.FourierDecayAlt.P.S3x9.block31_mul {A : Type} [CommRing A] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x * y) = b31 x * b11 y + b32 x * b21 y + b33 x * b31 y := by sorry
