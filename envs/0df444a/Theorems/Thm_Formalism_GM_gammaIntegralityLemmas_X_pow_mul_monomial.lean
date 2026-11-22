-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_X_pow_mul_monomial
-- name    : Formalism.GM.gammaIntegralityLemmas.X_pow_mul_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:39.336026+00:00
-- url     : https://prove2.me/theorems/22d5be15-166a-44c4-a401-f7a2c43dac1d
-- title:
--   gamma Integrality Lemmas: X pow mul monomial
-- statement:
--   The gamma Integrality Lemmas construction uses the X pow mul monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L929-L931
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L929-L931

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem Formalism.GM.gammaIntegralityLemmas.X_pow_mul_monomial (y : σ) (m : ℕ) (γ : σ →₀ ℕ) (h : ℚ_[p]) :
    (X y ^ m * monomial γ h : MvPolynomial σ ℚ_[p]) = monomial (γ + Finsupp.single y m) h := by sorry
