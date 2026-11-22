-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_isN_map
-- name    : Formalism.FourierDecayAlt.P.S3x3.isN_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:07:00.445829+00:00
-- url     : https://prove2.me/theorems/b8907db4-907f-4221-ac12-d2e6578d5ca3
-- title:
--   S3x3: is N map
-- statement:
--   The S3x3 construction uses the is N map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L248-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L248-L255

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

theorem Formalism.FourierDecayAlt.P.S3x3.isN_map {B : Type} [CommRing B] (f : A →+* B) {n : Matrix (Idx r k) (Idx r k) A}
    (hn : IsN n) : IsN (n.map f) := by sorry
