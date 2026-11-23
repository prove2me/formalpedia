-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_card_NU
-- name    : Formalism.FourierDecayAlt.P.S3x3.card_NU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:18.098817+00:00
-- url     : https://prove2.me/theorems/6ea36f3d-17df-4f15-8e87-ad823d63a84a
-- title:
--   S3x3: card NU
-- statement:
--   The S3x3 construction uses the card NU property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L503-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L503-L506

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

theorem Formalism.FourierDecayAlt.P.S3x3.card_NU : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsNU x} =
    Nat.card (upUniG A k) * Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsN x} := by sorry
