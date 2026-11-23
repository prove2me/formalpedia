-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Discr_minpoly_eq
-- name    : Formalism.FrobeniusOrbits.Discr.minpoly_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:26.365652+00:00
-- url     : https://prove2.me/theorems/a48e87ec-a249-40c8-8407-7f0f2bb40b07
-- title:
--   Discr: minpoly eq
-- statement:
--   The Discr construction uses the minpoly eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L77-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L77-L98

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield
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
open Formalism.FrobeniusOrbits.Discr
variable {K : Type*} [Field K] [NumberField K] {e : ℕ} {z : K}

theorem Formalism.FrobeniusOrbits.Discr.minpoly_eq (hz : IsPrimitiveRoot z (2 ^ (e + 2))) :
    minpoly ℚ⟮z + z⁻¹⟯ z = X ^ 2 - C (th z) * X + 1 := by sorry
