-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Discr_absNorm_different
-- name    : Formalism.FrobeniusOrbits.Discr.absNorm_different
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:56.553408+00:00
-- url     : https://prove2.me/theorems/742d35be-67df-433d-9371-46bb9762c569
-- title:
--   Discr: abs Norm different
-- statement:
--   The Discr construction uses the abs Norm different property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L128-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L128-L197

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
variable [IsCyclotomicExtension {2 ^ (e + 2)} ℚ K]

theorem Formalism.FrobeniusOrbits.Discr.absNorm_different (hz : IsPrimitiveRoot z (2 ^ (e + 2))) :
    Ideal.absNorm (differentIdeal (𝓞 ℚ⟮z + z⁻¹⟯) (𝓞 K)) = 4 := by sorry
