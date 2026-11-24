-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Bp_const_le
-- name    : Formalism.FourierDecayAlt.P.TBBx2.Bp.const_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:54:44.755535+00:00
-- url     : https://prove2.me/theorems/11d72b13-e803-4416-a9bf-834b17b4c0f5
-- title:
--   Bp: const le
-- statement:
--   The Bp construction uses the const le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L423-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L423-L469

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

theorem Formalism.FourierDecayAlt.P.TBBx2.Bp.const_le (C₃ CΛ C₀ C₂ Cκ b Λ κ₀ : ℝ) (r n₀ p₀ : ℕ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀)
    (hC₂ : 0 < C₂) (hb : 3 ≤ b) (hΛ : 1 ≤ Λ) (hΛb : Λ ≤ b ^ (CΛ * ((2 * r + 2 : ℕ) : ℝ)))
    (hκ : 0 < κ₀) (hκb : κ₀ ≤ b ^ (Cκ * ((2 * r + 2 : ℕ) : ℝ) ^ 2))
    (hn₀ : n₀ ≤ 30 * (r + 1) ^ 2 + 6) (hp₀ : (p₀ : ℝ) ≤ C₀ * (3 * ((r : ℝ) + 1)) + 1) :
    2 * (3 * b) ^ (2 * n₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (r + 1)) *
        b ^ (2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) ≤
      b ^ ((40 + CΛ + max 0 (Real.log C₂ / Real.log 3) + |Cκ| + 2 * C₃ * (3 * C₀ + 10)) *
        ((2 * r + 2 : ℕ) : ℝ) ^ 4) := by sorry
