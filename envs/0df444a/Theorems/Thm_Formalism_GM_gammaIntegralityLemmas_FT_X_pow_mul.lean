-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_FT_X_pow_mul
-- name    : Formalism.GM.gammaIntegralityLemmas.FT_X_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:01.537803+00:00
-- url     : https://prove2.me/theorems/4129ef20-12c0-4ce3-a055-2c761771fe74
-- title:
--   gamma Integrality Lemmas: FT X pow mul
-- statement:
--   The gamma Integrality Lemmas construction uses the FT X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L516-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L516-L519

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

theorem Formalism.GM.gammaIntegralityLemmas.FT_X_pow_mul (y : σ) (T : Finset (Fin r)) (hy : ∀ c ∈ T, w c ≠ y ∧ e c ≠ y) (m : ℕ)
    (G : MvPolynomial σ ℚ_[p]) : FT w e T (X y ^ m * G) = X y ^ m * FT w e T G := by sorry
