-- Prove2me | Theorems.Thm_Formalism_WachCohomologyFacts_PLenBound_length_le_of_span
-- name    : Formalism.WachCohomologyFacts.PLenBound.length_le_of_span
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:38:08.247814+00:00
-- url     : https://prove2.me/theorems/1aa374ff-700d-43df-a9e0-53e6e2c6d20b
-- title:
--   PLen Bound: length le of span
-- statement:
--   The PLen Bound construction uses the length le of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusContraction/FrobeniusContractionProofs/LenBound.lean#L9-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusContraction/FrobeniusContractionProofs/LenBound.lean#L9-L39

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

theorem Formalism.WachCohomologyFacts.PLenBound.length_le_of_span {P : Type} [AddCommGroup P] [Module O P] {ι : Type} [Fintype ι]
    (v : ι → P) (a : O) (hspan : Submodule.span O (Set.range v) = ⊤) (hv : ∀ i, a • v i = 0) :
    Module.length O P ≤ (Fintype.card ι : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by sorry
