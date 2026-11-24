-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Galois_mem_zpowers_neg_one
-- name    : Formalism.FrobeniusOrbits.Galois.mem_zpowers_neg_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:53:49.068621+00:00
-- url     : https://prove2.me/theorems/ba7ccffb-3603-455b-af5b-ad321cdccf47
-- title:
--   Galois: mem zpowers neg one
-- statement:
--   The Galois construction uses the mem zpowers neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L64-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L64-L74

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Galois
variable {K : Type*} [Field K] {N : ℕ} [NeZero N] {ζ : K}

theorem Formalism.FrobeniusOrbits.Galois.mem_zpowers_neg_one (x : (ZMod N)ˣ) :
    x ∈ Subgroup.zpowers (-1 : (ZMod N)ˣ) ↔ x = 1 ∨ x = -1 := by sorry
