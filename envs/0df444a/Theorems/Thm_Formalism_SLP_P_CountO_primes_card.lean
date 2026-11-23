-- Prove2me | Theorems.Thm_Formalism_SLP_P_CountO_primes_card
-- name    : Formalism.SLP.P.CountO.primes_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:47.976796+00:00
-- url     : https://prove2.me/theorems/243542d5-d113-474b-b216-e237a658f448
-- title:
--   Count O: primes card
-- statement:
--   The Count O construction uses the primes card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/CountO.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/CountO.lean#L11-L27

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO

theorem Formalism.SLP.P.CountO.primes_card (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    ∃ Ps : Finset (Ideal (𝓞 E)), Ps.card ≤ finrank ℚ E ∧
      ∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : ℕ) : 𝓞 E) ∈ P → P ∈ Ps := by sorry
