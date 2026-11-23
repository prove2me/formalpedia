-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_index_Kpp
-- name    : Formalism.FourierDecayAlt.P.S3x3.index_Kpp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:32.579204+00:00
-- url     : https://prove2.me/theorems/4f0e26da-8997-4efb-8c62-1abd1bd93b00
-- title:
--   S3x3: index Kpp
-- statement:
--   The S3x3 construction uses the index Kpp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L514-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L514-L519

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
variable (o : Type) [CommRing o] [IsLocalRing o] {r k : ℕ} (L : Levels o r k)

theorem Formalism.FourierDecayAlt.P.S3x3.index_Kpp : L.Kpp.index *
    (Nat.card (upUniG (IsLocalRing.ResidueField o) k) *
      Nat.card {x : Matrix (Idx r k) (Idx r k) (IsLocalRing.ResidueField o) // IsN x}) =
    Nat.card (GL (Idx r k) (IsLocalRing.ResidueField o)) := by sorry
