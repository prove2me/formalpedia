-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Bp_expo_le
-- name    : Formalism.FourierDecayAlt.P.TBBx2.Bp.expo_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:54:45.403902+00:00
-- url     : https://prove2.me/theorems/2e9bf2bd-3999-4074-b73a-c66451db7b6d
-- title:
--   Bp: expo le
-- statement:
--   The Bp construction uses the expo le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L365-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L365-L402

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2 Formalism.FourierDecayAlt.P.TBBx2.Bp
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB MeasureTheory
open scoped ENNReal

theorem Formalism.FourierDecayAlt.P.TBBx2.Bp.expo_le (C₃ CΛ C₀ L K : ℝ) (r n₀ p₀ : ℕ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀)
    (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hn₀ : n₀ ≤ 30 * (r + 1) ^ 2 + 6) (hp₀ : (p₀ : ℝ) ≤ C₀ * (3 * ((r : ℝ) + 1)) + 1) :
    1 + ((4 * n₀ : ℕ) : ℝ) + K * ((2 * r + 2 : ℕ) : ℝ) ^ 2 +
        (L + 2 * (CΛ * ((2 * r + 2 : ℕ) : ℝ))) * ((r + 1 : ℕ) : ℝ) +
        2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ) ≤
      (40 + CΛ + L + K + 2 * C₃ * (3 * C₀ + 10)) * ((2 * r + 2 : ℕ) : ℝ) ^ 4 := by sorry
