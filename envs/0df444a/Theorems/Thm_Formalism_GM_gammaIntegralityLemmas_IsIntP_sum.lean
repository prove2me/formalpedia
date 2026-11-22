-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_sum
-- name    : Formalism.GM.gammaIntegralityLemmas.IsIntP.sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:27.859813+00:00
-- url     : https://prove2.me/theorems/9c6c3efa-e287-47e0-bd66-307c0e464537
-- title:
--   Is Int P: sum
-- statement:
--   The Is Int P construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L726-L728
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L726-L728

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

theorem Formalism.GM.gammaIntegralityLemmas.IsIntP.sum {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ ℚ_[p]) (h : ∀ i ∈ s, IsIntP (P i)) :
    IsIntP (∑ i ∈ s, P i) := by sorry
