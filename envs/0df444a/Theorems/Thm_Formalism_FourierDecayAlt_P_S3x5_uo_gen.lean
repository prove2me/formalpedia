-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_uo_gen
-- name    : Formalism.FourierDecayAlt.P.S3x5.uo_gen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:14.169806+00:00
-- url     : https://prove2.me/theorems/bf5c2e44-bf8f-44be-b977-546ad05c34fa
-- title:
--   S3x5: uo gen
-- statement:
--   The S3x5 construction uses the uo gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L719-L738
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L719-L738

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
open Matrix Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K] [StarRing K]

theorem Formalism.FourierDecayAlt.P.S3x5.uo_gen {q : ℕ}
    (hUO : ∀ (b : ℕ) (J : Matrix (Fin b) (Fin b) K), Jᴴ = J → IsUnit J.det →
      (Nat.card {g : Matrix (Fin b) (Fin b) K // gᴴ * J * g = J} : ℝ) =
        (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b)
    {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι K) (hJ : Jᴴ = J) (hd : IsUnit J.det) :
    (Nat.card {g : Matrix ι ι K // gᴴ * J * g = J} : ℝ) =
      (q : ℝ) ^ ((Fintype.card ι) ^ 2) * densP (-1) q 1 (Fintype.card ι) := by sorry
