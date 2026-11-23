-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x9_cornerCount
-- name    : Formalism.FourierDecayAlt.P.S3x9.cornerCount
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:01.35267+00:00
-- url     : https://prove2.me/theorems/1d9c0b62-cb06-442b-9105-b6577018e67b
-- title:
--   S3x9: corner Count
-- statement:
--   The S3x9 construction uses the corner Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block32EqZeroOfUnipotent.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block32EqZeroOfUnipotent.lean#L16-L20

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

theorem Formalism.FourierDecayAlt.P.S3x9.cornerCount (K : Type) [Field K] [Fintype K] (r : ℕ) :
    Nat.card {X : Matrix (Fin r) (Fin r) K // ∀ (l : ℕ) (hl : l ≤ r), cm X l hl ≠ 0} =
      Fintype.card K ^ (r ^ 2 - r) * (Fintype.card K - 1) ^ r := by sorry
