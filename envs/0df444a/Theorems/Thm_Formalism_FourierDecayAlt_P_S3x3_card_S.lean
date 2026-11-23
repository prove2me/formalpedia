-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_card_S
-- name    : Formalism.FourierDecayAlt.P.S3x3.card_S
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:24.594002+00:00
-- url     : https://prove2.me/theorems/676a42d9-d54d-41b1-8cbd-ae09ce430a62
-- title:
--   S3x3: card S
-- statement:
--   The S3x3 construction uses the card S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L494-L501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L494-L501

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

theorem Formalism.FourierDecayAlt.P.S3x3.card_S : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsS x} =
    Nat.card (GL (Fin k) A) * Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsN x} := by sorry
