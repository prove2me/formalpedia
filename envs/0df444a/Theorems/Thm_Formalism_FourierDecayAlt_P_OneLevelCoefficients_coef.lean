-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_coef
-- name    : Formalism.FourierDecayAlt.P.OneLevelCoefficients.coef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:24.861439+00:00
-- url     : https://prove2.me/theorems/2225498c-68a7-47b6-ae8e-e25e13d1ac53
-- title:
--   One Level Coefficients: coef
-- statement:
--   The One Level Coefficients construction uses the coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OneLevelCoefficients.lean#L148-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OneLevelCoefficients.lean#L148-L196

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OneLevelCoefficients
open Formalism.FourierDecayAlt.TB Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]

theorem Formalism.FourierDecayAlt.P.OneLevelCoefficients.coef (D : Data E W) (Θ C₄ C₀ a e : ℝ) (hΘ : 1 ≤ Θ) (h4 : 1 ≤ C₄) (h0 : 2 * C₄ ≤ C₀)
    (hf : 1 ≤ D.f) (hS : D.SizesBelow Θ) (ha0 : 0 ≤ a) (ha : a ≤ 1) (_he0 : 0 ≤ e) (he : e ≤ 1)
    (i s : ℕ) (hs : 2 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.r + 1) :
    √((1 + a) * (1 + e) * C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') ≤
      ((C₀ / Θ) ^ D.f) ^ (s - 1) := by sorry
