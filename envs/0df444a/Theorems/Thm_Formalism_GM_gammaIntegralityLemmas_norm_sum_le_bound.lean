-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_sum_le_bound
-- name    : Formalism.GM.gammaIntegralityLemmas.norm_sum_le_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:24:22.581373+00:00
-- url     : https://prove2.me/theorems/5c5a3a25-2b79-4da0-afa8-ea89c3a50829
-- title:
--   gamma Integrality Lemmas: norm sum le bound
-- statement:
--   The gamma Integrality Lemmas construction uses the norm sum le bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L261-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L261-L269

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
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem Formalism.GM.gammaIntegralityLemmas.norm_sum_le_bound {ι : Type} (s : Finset ι) (f : ι → ℚ_[p]) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ i ∈ s, ‖f i‖ ≤ K) : ‖∑ i ∈ s, f i‖ ≤ K := by sorry
