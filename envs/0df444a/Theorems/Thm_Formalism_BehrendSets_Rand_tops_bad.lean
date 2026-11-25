-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Rand_tops_bad
-- name    : Formalism.BehrendSets.Rand.tops_bad
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:19:55.644213+00:00
-- url     : https://prove2.me/theorems/0f4cf6c4-0559-56be-b82f-d3cbd552d276
-- title:
--   Rand: tops bad
-- statement:
--   The Rand construction uses the tops bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L133-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L133-L174

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Rand
variable {α : Type} [DecidableEq α]

theorem Formalism.BehrendSets.Rand.tops_bad (X : Finset α) (δ : ℝ) (L K : ℕ) (t : α) (𝒲 : Finset (Finset α))
    (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hW : ∀ W ∈ 𝒲, W.card ≤ L) :
    prob X δ (fun T => t ∈ T ∧ ∃ W ∈ 𝒲, K + 1 ≤ (T ∩ W).card)
      ≤ δ * 𝒲.card * ((L : ℝ) * δ) ^ K := by sorry
