-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_zeta_not_mem
-- name    : Formalism.FrobeniusOrbits.RealCyclotomicSubfield.zeta_not_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:35:23.143195+00:00
-- url     : https://prove2.me/theorems/d66f015e-a93d-49c1-8bd5-b0db8bcbe9fa
-- title:
--   Real Cyclotomic Subfield: zeta not mem
-- statement:
--   The Real Cyclotomic Subfield construction uses the zeta not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean#L96-L99

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

theorem Formalism.FrobeniusOrbits.RealCyclotomicSubfield.zeta_not_mem {e : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2))) : ζ ∉ F1 ζ := by sorry
