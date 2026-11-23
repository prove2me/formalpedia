-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_isN_of_map
-- name    : Formalism.FourierDecayAlt.P.S3x3.isN_of_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:43.143059+00:00
-- url     : https://prove2.me/theorems/77da01cf-56d6-4a9f-855f-1abeb44d246d
-- title:
--   S3x3: is N of map
-- statement:
--   The S3x3 construction uses the is N of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L257-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L257-L264

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

theorem Formalism.FourierDecayAlt.P.S3x3.isN_of_map {B : Type} [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    {n : Matrix (Idx r k) (Idx r k) A} (hn : IsN (n.map f)) : IsN n := by sorry
