-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_galMap_injective
-- name    : Formalism.TwoAdicCyclotomicDecomposition.galMap_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:29:57.898882+00:00
-- url     : https://prove2.me/theorems/338bc508-90ab-44b6-8ba4-d6203b19dfc5
-- title:
--   Two Adic Cyclotomic Decomposition: gal Map injective
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the gal Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L183-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L183-L193

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

theorem Formalism.TwoAdicCyclotomicDecomposition.galMap_injective (h : IsLayer n q d ζ a b) (hq0 : q ≠ 0) (hd0 : d ≠ 0) :
    Function.Injective (galMap h.1 a b) := by sorry
