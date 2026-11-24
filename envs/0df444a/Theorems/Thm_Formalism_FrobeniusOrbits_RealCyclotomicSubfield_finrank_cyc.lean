-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_finrank_cyc
-- name    : Formalism.FrobeniusOrbits.RealCyclotomicSubfield.finrank_cyc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:04.321824+00:00
-- url     : https://prove2.me/theorems/749a463d-73bd-4a89-87a6-f73ceb82d8c9
-- title:
--   Real Cyclotomic Subfield: finrank cyc
-- statement:
--   The Real Cyclotomic Subfield construction uses the finrank cyc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean#L107-L114

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

theorem Formalism.FrobeniusOrbits.RealCyclotomicSubfield.finrank_cyc {e : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2))) :
    Module.finrank ℚ ℚ⟮ζ⟯ = 2 ^ (e + 1) := by sorry
