-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layer_finrank_ge
-- name    : Formalism.TwoAdicCyclotomicDecomposition.layer_finrank_ge
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:30:29.465859+00:00
-- url     : https://prove2.me/theorems/352e3dd3-1dea-4c9e-8cf9-c8ae8697cbb3
-- title:
--   Two Adic Cyclotomic Decomposition: layer finrank ge
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the layer finrank ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L209-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L209-L289

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

theorem Formalism.TwoAdicCyclotomicDecomposition.layer_finrank_ge (h : IsLayer n q d ζ a b) (hn : 1 ≤ n) (hqd : HypOdd q d)
    [IsGalois ℚ L] : 2 ^ (n + 1) ≤ Module.finrank ℚ L := by sorry
