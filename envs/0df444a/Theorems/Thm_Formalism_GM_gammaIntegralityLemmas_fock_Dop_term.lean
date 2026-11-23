-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_Dop_term
-- name    : Formalism.GM.gammaIntegralityLemmas.fock_Dop_term
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:50.966338+00:00
-- url     : https://prove2.me/theorems/3346346d-3c1a-44ce-bec6-d9e582aade42
-- title:
--   gamma Integrality Lemmas: fock Dop term
-- statement:
--   The gamma Integrality Lemmas construction uses the fock Dop term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L933-L992
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L933-L992

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

theorem Formalism.GM.gammaIntegralityLemmas.fock_Dop_term (x y : σ) (hxy : x ≠ y) (a a' m : ℕ) (β₀ β₀' : σ →₀ ℕ) (h h' : ℚ_[p]) :
    Formalism.GM.M.fock p ((Dop x y ^ a) (X y ^ m * monomial (β₀ + a • (Finsupp.single x 1 + Finsupp.single y 1)) h))
      ((Dop x y ^ a') (X y ^ m * monomial (β₀' + a' • (Finsupp.single x 1 + Finsupp.single y 1)) h')) =
    if β₀ = β₀' then
      h * h' * (((β₀ x + a).descFactorial a : ℕ) : ℚ_[p]) * (((β₀ x + a').descFactorial a' : ℕ) : ℚ_[p]) *
        wf (β₀ + Finsupp.single y a) * (((m + (β₀ y + a)).choose (β₀ y + a) : ℕ) : ℚ_[p]) *
        (m.factorial : ℚ_[p]) * ((((m + (β₀ y + a'))).descFactorial a' : ℕ) : ℚ_[p])
    else 0 := by sorry
