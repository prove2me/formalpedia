-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layer_isGalois
-- name    : Formalism.TwoAdicCyclotomicDecomposition.layer_isGalois
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:30:24.2808+00:00
-- url     : https://prove2.me/theorems/35b08162-9ddc-469f-aad7-332b8385679a
-- title:
--   Two Adic Cyclotomic Decomposition: layer is Galois
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the layer is Galois property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L165-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L165-L169

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

theorem Formalism.TwoAdicCyclotomicDecomposition.layer_isGalois (h : IsLayer n q d ζ a b) : IsGalois ℚ L := by sorry
