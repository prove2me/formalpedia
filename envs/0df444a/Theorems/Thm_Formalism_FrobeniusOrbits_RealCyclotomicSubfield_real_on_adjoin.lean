-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_real_on_adjoin
-- name    : Formalism.FrobeniusOrbits.RealCyclotomicSubfield.real_on_adjoin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:00:19.625585+00:00
-- url     : https://prove2.me/theorems/8286f727-4d5a-49f0-9707-145497e2a20a
-- title:
--   Real Cyclotomic Subfield: real on adjoin
-- statement:
--   The Real Cyclotomic Subfield construction uses the real on adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean#L45-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean#L45-L57

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.RealCyclotomicSubfield

theorem Formalism.FrobeniusOrbits.RealCyclotomicSubfield.real_on_adjoin {K : Type*} [Field K] [Algebra ℚ K] (t : K) (φ : K →+* ℂ)
    (ht : starRingEnd ℂ (φ t) = φ t) : ∀ x ∈ ℚ⟮t⟯, starRingEnd ℂ (φ x) = φ x := by sorry
