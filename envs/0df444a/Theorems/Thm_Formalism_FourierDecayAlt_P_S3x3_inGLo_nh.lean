-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_inGLo_nh
-- name    : Formalism.FourierDecayAlt.P.S3x3.inGLo_nh
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:37.897295+00:00
-- url     : https://prove2.me/theorems/3200ed3b-63a4-40ed-86c3-719712792e2c
-- title:
--   S3x3: in GLo nh
-- statement:
--   The S3x3 construction uses the in GLo nh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L323-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L323-L333

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
variable (o : Type) [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]
variable [IsFractionRing o k0]

theorem Formalism.FourierDecayAlt.P.S3x3.inGLo_nh {r k : ℕ} {n : Matrix (Idx r k) (Idx r k) k0} {h : Matrix (Fin k) (Fin k) k0}
    (hn : IsN n) (hh : IsUnit h.det) : InGLo o (n * hEmb r h) ↔ InGLo o n ∧ InGLo o h := by sorry
