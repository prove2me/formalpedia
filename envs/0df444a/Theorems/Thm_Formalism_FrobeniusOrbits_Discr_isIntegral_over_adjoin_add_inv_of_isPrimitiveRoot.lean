-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Discr_isIntegral_over_adjoin_add_inv_of_isPrimitiveRoot
-- name    : Formalism.FrobeniusOrbits.Discr.isIntegral_over_adjoin_add_inv_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:26.029805+00:00
-- url     : https://prove2.me/theorems/262d7d46-41e1-411b-90ea-62858ffa6616
-- title:
--   Discr: is Integral over adjoin add inv of is Primitive Root
-- statement:
--   The Discr construction uses the is Integral over adjoin add inv of is Primitive Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L74-L75

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

theorem Formalism.FrobeniusOrbits.Discr.isIntegral_over_adjoin_add_inv_of_isPrimitiveRoot (hz : IsPrimitiveRoot z (2 ^ (e + 2))) : IsIntegral ℚ⟮z + z⁻¹⟯ z := by sorry
