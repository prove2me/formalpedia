-- Prove2me | Theorems.Thm_Formalism_WachCohomologyFacts_PLenBound_length_quot_pow_le
-- name    : Formalism.WachCohomologyFacts.PLenBound.length_quot_pow_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:37:33.842942+00:00
-- url     : https://prove2.me/theorems/b7926543-95e9-44b8-bc5e-d11678ca5706
-- title:
--   PLen Bound: length quot pow le
-- statement:
--   The PLen Bound construction uses the length quot pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusContraction/FrobeniusContractionProofs/LenBound.lean#L41-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusContraction/FrobeniusContractionProofs/LenBound.lean#L41-L85

import Definitions.Def_Formalism_FrobeniusContraction_Statement
import Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_LenBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WachCohomologyFacts Formalism.WachCohomologyFacts.PLenBound
variable {O : Type} [CommRing O]

theorem Formalism.WachCohomologyFacts.PLenBound.length_quot_pow_le (a : O) (e : ℕ) :
    Module.length O (O ⧸ Ideal.span {a ^ e}) ≤ (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by sorry
