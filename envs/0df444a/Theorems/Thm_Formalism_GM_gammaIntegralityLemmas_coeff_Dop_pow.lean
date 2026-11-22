-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_coeff_Dop_pow
-- name    : Formalism.GM.gammaIntegralityLemmas.coeff_Dop_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:49.618795+00:00
-- url     : https://prove2.me/theorems/b4d0acea-4ed6-4375-803d-b40b60a75f9a
-- title:
--   gamma Integrality Lemmas: coeff Dop pow
-- statement:
--   The gamma Integrality Lemmas construction uses the coeff Dop pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L416-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L416-L443

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

theorem Formalism.GM.gammaIntegralityLemmas.coeff_Dop_pow (u v : σ) (huv : u ≠ v) (a : ℕ) (G : MvPolynomial σ ℚ_[p]) (β : σ →₀ ℕ) :
    coeff β ((Dop u v ^ a) G) = coeff (β + a • (Finsupp.single u 1 + Finsupp.single v 1)) G *
      (((β u + a).descFactorial a : ℕ) : ℚ_[p]) * (((β v + a).descFactorial a : ℕ) : ℚ_[p]) := by sorry
