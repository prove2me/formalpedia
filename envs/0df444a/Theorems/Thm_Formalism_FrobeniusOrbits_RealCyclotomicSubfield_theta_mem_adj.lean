-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_theta_mem_adj
-- name    : Formalism.FrobeniusOrbits.RealCyclotomicSubfield.theta_mem_adj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:26.695802+00:00
-- url     : https://prove2.me/theorems/a2d3ad96-972e-4eec-b25d-0d11c85c4f56
-- title:
--   Real Cyclotomic Subfield: theta mem adj
-- statement:
--   The Real Cyclotomic Subfield construction uses the theta mem adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean#L101-L102

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

theorem Formalism.FrobeniusOrbits.RealCyclotomicSubfield.theta_mem_adj (ζ : L) : ζ + ζ⁻¹ ∈ ℚ⟮ζ⟯ := by sorry
