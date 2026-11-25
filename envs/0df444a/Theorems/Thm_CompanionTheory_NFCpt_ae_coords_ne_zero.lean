-- Prove2me | Theorems.Thm_CompanionTheory_NFCpt_ae_coords_ne_zero
-- name    : CompanionTheory.NFCpt.ae_coords_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:16:23.467695+00:00
-- url     : https://prove2.me/theorems/d8e43e4e-2398-5bcf-9899-8b1daae6ecb1
-- title:
--   NFCpt: ae coords ne zero
-- statement:
--   The NFCpt construction uses the ae coords ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/DiscreteGroupWaves/IntegralEqOfSqrtCauchy.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/DiscreteGroupWaves/IntegralEqOfSqrtCauchy.lean#L7-L12

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

theorem CompanionTheory.NFCpt.ae_coords_ne_zero (n : ℕ) : ∀ᵐ c : Fin n → ℂ, ∀ a, c a ≠ 0 := by sorry
