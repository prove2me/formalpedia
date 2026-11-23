-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_exists_frame
-- name    : Formalism.FourierDecayAlt.P.S3x5.exists_frame
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:30.226675+00:00
-- url     : https://prove2.me/theorems/684a6d83-e3c8-4683-bdcb-ab43cbf4f990
-- title:
--   S3x5: exists frame
-- statement:
--   The S3x5 construction uses the exists frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L485-L557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L485-L557

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

theorem Formalism.FourierDecayAlt.P.S3x5.exists_frame (htr : ∃ μ : K, μ + star μ ≠ 0)
    (hnorm : ∀ t : K, t ≠ 0 → star t = t → ∃ l : K, star l * l = t)
    {ν : Type} [Fintype ν] [DecidableEq ν] (J : Matrix ν ν K) (hJ : Jᴴ = J) (hd : IsUnit J.det)
    (m : ℕ) (hm : m ≤ Fintype.card ν) : ∃ X : Matrix ν (Fin m) K, Xᴴ * J * X = 1 := by sorry
