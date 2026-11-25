-- Prove2me | Theorems.Thm_CompanionTheory_NFCpt_tower_integral
-- name    : CompanionTheory.NFCpt.tower_integral
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:37.03383+00:00
-- url     : https://prove2.me/theorems/a3eeeac6-29ba-4ba2-b05e-778444bfc3df
-- title:
--   NFCpt: tower integral
-- statement:
--   The NFCpt construction uses the tower integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/DiscreteGroupWaves/IntegralEqOfSqrtCauchy.lean#L18-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/DiscreteGroupWaves/IntegralEqOfSqrtCauchy.lean#L18-L80

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_DiscreteGroupWaves_IntegralEqOfSqrtCauchy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.NFCpt
open MeasureTheory Filter Topology

theorem CompanionTheory.NFCpt.tower_integral : ∀ (n : ℕ) (E : (j : ℕ) → (Fin j → ℂ) → ℝ),
    AEStronglyMeasurable (E n) volume → (∀ c, (∀ a, c a ≠ 0) → 0 ≤ E n c) →
    (∀ j, j < n → ∀ c : Fin j → ℂ, (∀ a, c a ≠ 0) →
      Integrable (fun t : ℂ => E (j + 1) (Fin.snoc c t)) ∧ ∫ t : ℂ, E (j + 1) (Fin.snoc c t) = E j c) →
    Integrable (E n) ∧ ∫ c, E n c = E 0 (fun a => a.elim0)
  := by sorry
