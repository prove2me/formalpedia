-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_fix_on_adjoin
-- name    : Formalism.FrobeniusOrbits.RealCyclotomicSubfield.fix_on_adjoin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:17.363458+00:00
-- url     : https://prove2.me/theorems/0fb9e63d-18bd-47bd-b80e-a088fb8c85e8
-- title:
--   Real Cyclotomic Subfield: fix on adjoin
-- statement:
--   The Real Cyclotomic Subfield construction uses the fix on adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean#L59-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean#L59-L81

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

theorem Formalism.FrobeniusOrbits.RealCyclotomicSubfield.fix_on_adjoin {L : Type*} [Field L] [Algebra ℚ L] {E : IntermediateField ℚ L}
    (σ : E ≃ₐ[ℚ] E) {t : L} (hle : ℚ⟮t⟯ ≤ E)
    (hσ : ((σ ⟨t, hle (mem_adjoin_simple_self ℚ t)⟩ : E) : L) = t) :
    ∀ x : E, (x : L) ∈ ℚ⟮t⟯ → σ x = x := by sorry
