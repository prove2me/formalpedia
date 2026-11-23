-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_exists_G
-- name    : Formalism.FourierDecayAlt.P.S3x5.exists_G
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:16.417489+00:00
-- url     : https://prove2.me/theorems/26c08a83-ba0a-4c3d-8a8f-5ebe4ad61a9c
-- title:
--   S3x5: exists G
-- statement:
--   The S3x5 construction uses the exists G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L559-L579
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L559-L579

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

theorem Formalism.FourierDecayAlt.P.S3x5.exists_G (htr : ∃ μ : K, μ + star μ ≠ 0)
    (hnorm : ∀ t : K, t ≠ 0 → star t = t → ∃ l : K, star l * l = t)
    {μ ν : Type} [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
    (hcard : Fintype.card μ = Fintype.card ν) (J : Matrix μ μ K) (D : Matrix ν ν K)
    (hJ : Jᴴ = J) (hdJ : IsUnit J.det) (hD : Dᴴ = D) (hdD : IsUnit D.det) :
    ∃ (G : Matrix μ ν K) (G' : Matrix ν μ K), G * G' = 1 ∧ G' * G = 1 ∧ Gᴴ * J * G = D := by sorry
