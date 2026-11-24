-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Galois_fixingSubgroup_hostE_le
-- name    : Formalism.FrobeniusOrbits.Galois.fixingSubgroup_hostE_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:52:25.936545+00:00
-- url     : https://prove2.me/theorems/b32c452b-095a-4d59-843c-6fda7fee75b4
-- title:
--   Galois: fixing Subgroup host E le
-- statement:
--   The Galois construction uses the fixing Subgroup host E le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L230-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L230-L257

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

theorem Formalism.FrobeniusOrbits.Galois.fixingSubgroup_hostE_le (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    (hostE ζ a b).fixingSubgroup ≤ Subgroup.zpowers (tau0 hqd h) := by sorry
