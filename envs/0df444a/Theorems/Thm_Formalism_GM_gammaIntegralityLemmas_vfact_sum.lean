-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_vfact_sum
-- name    : Formalism.GM.gammaIntegralityLemmas.vfact_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:31.808522+00:00
-- url     : https://prove2.me/theorems/17dfd0fb-b29a-419a-a749-e47050b77782
-- title:
--   gamma Integrality Lemmas: vfact sum
-- statement:
--   The gamma Integrality Lemmas construction uses the vfact sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L222-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L222-L233

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

theorem Formalism.GM.gammaIntegralityLemmas.vfact_sum {ι : Type} (s : Finset ι) (α : ι → ℕ) {T B : ℕ} (h : ∑ i ∈ s, α i ≤ T)
    (hB : Nat.log p T ≤ B) :
    padicValNat p (∑ i ∈ s, α i).factorial ≤ ∑ i ∈ s, padicValNat p (α i).factorial + s.card * B := by sorry
