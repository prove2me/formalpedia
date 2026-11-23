-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_nd_count
-- name    : Formalism.FourierDecayAlt.P.S3x5.nd_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:23.461157+00:00
-- url     : https://prove2.me/theorems/27af92c3-67cf-4d59-99e9-883ce6aa2c10
-- title:
--   S3x5: nd count
-- statement:
--   The S3x5 construction uses the nd count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L872-L950
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L872-L950

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

theorem Formalism.FourierDecayAlt.P.S3x5.nd_count {q : ℕ} (hq : 2 ≤ q)
    (htr : ∃ μ : K, μ + star μ ≠ 0)
    (hnorm : ∀ t : K, t ≠ 0 → star t = t → ∃ l : K, star l * l = t)
    (hUO : ∀ (b : ℕ) (J : Matrix (Fin b) (Fin b) K), Jᴴ = J → IsUnit J.det →
      (Nat.card {g : Matrix (Fin b) (Fin b) K // gᴴ * J * g = J} : ℝ) =
        (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b)
    (hW : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y)
    {α : Type} [Fintype α] [DecidableEq α] (n : ℕ) (J : Matrix (Fin n) (Fin n) K) (T : Matrix α α K)
    (hJ : Jᴴ = J) (hdJ : IsUnit J.det) (hT : Tᴴ = T) (hdT : IsUnit T.det) :
    (Nat.card {X : Matrix (Fin n) α K // Xᴴ * J * X = T} : ℝ) =
      (q : ℝ) ^ ((2 * n * (Fintype.card α) : ℤ) - (Fintype.card α) ^ 2) *
        densP (-1) q ((n : ℤ) - Fintype.card α + 1) n := by sorry
