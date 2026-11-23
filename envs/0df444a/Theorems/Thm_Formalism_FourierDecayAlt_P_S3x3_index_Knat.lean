-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_index_Knat
-- name    : Formalism.FourierDecayAlt.P.S3x3.index_Knat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:31.244817+00:00
-- url     : https://prove2.me/theorems/4adb4f4c-d014-4e93-817c-cfde0e94654e
-- title:
--   S3x3: index Knat
-- statement:
--   The S3x3 construction uses the index Knat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L521-L526
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L521-L526

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

theorem Formalism.FourierDecayAlt.P.S3x3.index_Knat : L.Knat.index *
    (Nat.card (GL (Fin k) (IsLocalRing.ResidueField o)) *
      Nat.card {x : Matrix (Idx r k) (Idx r k) (IsLocalRing.ResidueField o) // IsN x}) =
    Nat.card (GL (Idx r k) (IsLocalRing.ResidueField o)) := by sorry
