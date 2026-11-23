-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_card_fibre
-- name    : Formalism.FourierDecayAlt.P.S3x5.card_fibre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:56.939419+00:00
-- url     : https://prove2.me/theorems/bfab47c3-6488-40c6-91aa-dc9f1ef158a6
-- title:
--   S3x5: card fibre
-- statement:
--   The S3x5 construction uses the card fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L665-L697
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L665-L697

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix
variable {K : Type} [Field K] [Fintype K] [StarRing K]
omit [StarRing K]

theorem Formalism.FourierDecayAlt.P.S3x5.card_fibre {n a c : ℕ} (A : Matrix (Fin a) (Fin n) K) (hA : A.rank = a)
    (B : Matrix (Fin a) (Fin c) K) :
    Nat.card {Y : Matrix (Fin n) (Fin c) K // A * Y = B} = Fintype.card K ^ ((n - a) * c) := by sorry
