-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_FT_pow_X_pow_mul
-- name    : Formalism.GM.gammaIntegralityLemmas.FT_pow_X_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:34.764803+00:00
-- url     : https://prove2.me/theorems/7077bfc4-13ea-4e5d-bf09-3a7ecea0f5e4
-- title:
--   gamma Integrality Lemmas: FT pow X pow mul
-- statement:
--   The gamma Integrality Lemmas construction uses the FT pow X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L521-L525
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L521-L525

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
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)

theorem Formalism.GM.gammaIntegralityLemmas.FT_pow_X_pow_mul (y : σ) (T : Finset (Fin r)) (hy : ∀ c ∈ T, w c ≠ y ∧ e c ≠ y) (m b : ℕ)
    (G : MvPolynomial σ ℚ_[p]) : (FT w e T ^ b) (X y ^ m * G) = X y ^ m * (FT w e T ^ b) G := by sorry
