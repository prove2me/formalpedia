-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_intPol_coeff
-- name    : Formalism.GM.gammaIntegralityLemmas.intPol_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:58.344802+00:00
-- url     : https://prove2.me/theorems/13b27236-7790-4e0d-be2f-d2ae45cde1e9
-- title:
--   gamma Integrality Lemmas: int Pol coeff
-- statement:
--   The gamma Integrality Lemmas construction uses the int Pol coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L890-L895
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L890-L895

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
variable {N r : ℕ}

theorem Formalism.GM.gammaIntegralityLemmas.intPol_coeff {σ : Type} (f : MvPolynomial σ ℚ_[p]) (hf : f ∈ IntPol p σ) :
    ∀ μ, ‖coeff μ f‖ ≤ 1 := by sorry
