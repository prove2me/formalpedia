-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_Dop_X_pow_mul
-- name    : Formalism.GM.gammaIntegralityLemmas.Dop_X_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:05.9598+00:00
-- url     : https://prove2.me/theorems/4215ff36-ceea-49a3-a481-58d7ae7d3e3c
-- title:
--   gamma Integrality Lemmas: Dop X pow mul
-- statement:
--   The gamma Integrality Lemmas construction uses the Dop X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L487-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L487-L489

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
variable {σ : Type} [DecidableEq σ]

theorem Formalism.GM.gammaIntegralityLemmas.Dop_X_pow_mul (u v y : σ) (huy : u ≠ y) (hvy : v ≠ y) (m : ℕ) (G : MvPolynomial σ ℚ_[p]) :
    Dop u v (X y ^ m * G) = X y ^ m * Dop u v G := by sorry
