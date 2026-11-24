-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Galois_mem_hostE_iff
-- name    : Formalism.FrobeniusOrbits.Galois.mem_hostE_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:52:51.159851+00:00
-- url     : https://prove2.me/theorems/208ce720-2e44-403a-b5ab-21728796b194
-- title:
--   Galois: mem host E iff
-- statement:
--   The Galois construction uses the mem host E iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L267-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L267-L269

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
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.FrobeniusOrbits.Galois.mem_hostE_iff (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (x : L) :
    x ∈ hostE ζ a b ↔ tau0 hqd h x = x := by sorry
