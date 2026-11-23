-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_herm_count_star
-- name    : Formalism.FourierDecayAlt.P.S3x5.herm_count_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:21.965851+00:00
-- url     : https://prove2.me/theorems/17ff7740-b565-41dc-af73-5d14e74be973
-- title:
--   S3x5: herm count star
-- statement:
--   The S3x5 construction uses the herm count star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L1032-L1144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L1032-L1144

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

theorem Formalism.FourierDecayAlt.P.S3x5.herm_count_star {q : ℕ} (hs : ∀ x : K, star x = x ^ q) (hc : Fintype.card K = q ^ 2)
    (hUO : ∀ (b : ℕ) (J : Matrix (Fin b) (Fin b) K), Jᴴ = J → IsUnit J.det →
      (Nat.card {g : Matrix (Fin b) (Fin b) K // gᴴ * J * g = J} : ℝ) =
        (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b)
    (hW : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y)
    (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin a) (Fin a) K)
    (hJ : Jᴴ = J) (hdJ : IsUnit J.det) (hT : Tᴴ = T) :
    (Nat.card {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T} : ℝ) =
      (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) *
        densP (-1) q ((n : ℤ) - a - ((a : ℤ) - T.rank) + 1) n := by sorry
