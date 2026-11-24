-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Discr_discr_F
-- name    : Formalism.FrobeniusOrbits.Discr.discr_F
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:17.56836+00:00
-- url     : https://prove2.me/theorems/b40750c1-d914-4f8e-998a-dee271abb74d
-- title:
--   Discr: discr F
-- statement:
--   The Discr construction uses the discr F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L212-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L212-L246

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

theorem Formalism.FrobeniusOrbits.Discr.discr_F (hz : IsPrimitiveRoot z (2 ^ (e + 2))) :
    discr ℚ⟮z + z⁻¹⟯ = 2 ^ (2 ^ e * (e + 1) - 1) := by sorry
