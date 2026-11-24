-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_maxReal_iff
-- name    : Formalism.FrobeniusOrbits.RealCyclotomicSubfield.maxReal_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:41.305089+00:00
-- url     : https://prove2.me/theorems/1b008517-3090-47c3-869a-dc49610d113c
-- title:
--   Real Cyclotomic Subfield: max Real iff
-- statement:
--   The Real Cyclotomic Subfield construction uses the max Real iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean#L195-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean#L195-L268

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
variable {L : Type} [Field L] [NumberField L]

theorem Formalism.FrobeniusOrbits.RealCyclotomicSubfield.maxReal_iff {e : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2))) :
    ∀ x : ℚ⟮ζ⟯, x ∈ maximalRealSubfield ℚ⟮ζ⟯ ↔ (x : L) ∈ F1 ζ := by sorry
