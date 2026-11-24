-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Discr_zeta_not_mem
-- name    : Formalism.FrobeniusOrbits.Discr.zeta_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:59.654921+00:00
-- url     : https://prove2.me/theorems/cb3da70e-5076-4c47-b7b0-f091c0b2b319
-- title:
--   Discr: zeta not mem
-- statement:
--   The Discr construction uses the zeta not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L62-L68

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

theorem Formalism.FrobeniusOrbits.Discr.zeta_not_mem (hz : IsPrimitiveRoot z (2 ^ (e + 2))) : z ∉ ℚ⟮z + z⁻¹⟯ := by sorry
