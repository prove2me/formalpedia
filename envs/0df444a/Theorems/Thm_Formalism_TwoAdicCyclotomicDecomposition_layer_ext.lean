-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layer_ext
-- name    : Formalism.TwoAdicCyclotomicDecomposition.layer_ext
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:30:24.012802+00:00
-- url     : https://prove2.me/theorems/a6570778-55a1-4b32-930c-95b11bfcba28
-- title:
--   Two Adic Cyclotomic Decomposition: layer ext
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the layer ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L171-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L171-L181

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

theorem Formalism.TwoAdicCyclotomicDecomposition.layer_ext (h : IsLayer n q d ζ a b) {σ τ : Gal(L/ℚ)} (h1 : σ ζ = τ ζ) (h2 : σ a = τ a)
    (h3 : σ b = τ b) : σ = τ := by sorry
