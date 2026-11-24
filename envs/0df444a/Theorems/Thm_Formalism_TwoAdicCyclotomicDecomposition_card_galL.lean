-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_card_galL
-- name    : Formalism.TwoAdicCyclotomicDecomposition.card_galL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:47.737835+00:00
-- url     : https://prove2.me/theorems/b62b4b97-3e98-4f1e-a35a-0e50c70cbfdf
-- title:
--   Two Adic Cyclotomic Decomposition: card gal L
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the card gal L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L201-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L201-L207

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Polynomial
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {n q d : ℕ} {ζ a b : L}

theorem Formalism.TwoAdicCyclotomicDecomposition.card_galL (hn : 1 ≤ n) : Nat.card (GalL n) = 2 ^ (n + 1) := by sorry
