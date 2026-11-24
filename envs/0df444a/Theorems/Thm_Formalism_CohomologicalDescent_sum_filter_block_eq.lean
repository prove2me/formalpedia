-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_sum_filter_block_eq
-- name    : Formalism.CohomologicalDescent.sum_filter_block_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:37:41.910585+00:00
-- url     : https://prove2.me/theorems/6a2c402f-9e22-4148-9a8f-943289196dd8
-- title:
--   Cohomological Descent: sum filter block eq
-- statement:
--   The Cohomological Descent construction uses the sum filter block eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightExchangeChainHolds.lean#L18-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightExchangeChainHolds.lean#L18-L49

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_WEChain
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ContentLinkageHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeBoundHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeChainHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.CohomologicalDescent

theorem Formalism.CohomologicalDescent.sum_filter_block_eq (k j t q : ℕ) (U : Fin (k + j + t + q) → ℤ) (b : ℤ)
    (hblock : ∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U a = b + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) :
    ∑ a ∈ Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U a =
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ)) := by sorry
