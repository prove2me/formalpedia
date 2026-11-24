-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Galois_hcl_eq_iff
-- name    : Formalism.FrobeniusOrbits.Galois.hcl_eq_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:52:49.892927+00:00
-- url     : https://prove2.me/theorems/a1f96377-ac27-4ac9-9fe2-c58049b65cad
-- title:
--   Galois: hcl eq iff
-- statement:
--   The Galois construction uses the hcl eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L78-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L78-L91

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

theorem Formalism.FrobeniusOrbits.Galois.hcl_eq_iff (e : ℕ) (u c : (ZMod (2 ^ (e + 2)))ˣ) :
    hcl e u = hcl e c ↔ u = c ∨ u = -c := by sorry
