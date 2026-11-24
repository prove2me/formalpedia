-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_Dop_pow_monomial_add
-- name    : Formalism.GM.gammaIntegralityLemmas.Dop_pow_monomial_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:36.181937+00:00
-- url     : https://prove2.me/theorems/976504ef-561f-4219-a5ad-af3b43077399
-- title:
--   gamma Integrality Lemmas: Dop pow monomial add
-- statement:
--   The gamma Integrality Lemmas construction uses the Dop pow monomial add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L458-L467
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L458-L467

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

theorem Formalism.GM.gammaIntegralityLemmas.Dop_pow_monomial_add (u v : σ) (huv : u ≠ v) (a : ℕ) (δ : σ →₀ ℕ) (h : ℚ_[p]) :
    (Dop u v ^ a) (monomial (δ + a • (Finsupp.single u 1 + Finsupp.single v 1)) h) =
      monomial δ (h * (((δ u + a).descFactorial a : ℕ) : ℚ_[p]) * (((δ v + a).descFactorial a : ℕ) : ℚ_[p])) := by sorry
