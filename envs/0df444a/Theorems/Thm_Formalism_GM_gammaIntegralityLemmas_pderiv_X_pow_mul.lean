-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_pderiv_X_pow_mul
-- name    : Formalism.GM.gammaIntegralityLemmas.pderiv_X_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:55.620802+00:00
-- url     : https://prove2.me/theorems/09ea6d46-ca84-4c2a-99af-81d1a1323a7d
-- title:
--   gamma Integrality Lemmas: pderiv X pow mul
-- statement:
--   The gamma Integrality Lemmas construction uses the pderiv X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L480-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L480-L485

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

theorem Formalism.GM.gammaIntegralityLemmas.pderiv_X_pow_mul (i y : σ) (hiy : i ≠ y) (m : ℕ) (G : MvPolynomial σ ℚ_[p]) :
    pderiv i (X y ^ m * G) = X y ^ m * pderiv i G := by sorry
