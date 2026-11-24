-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Discr_totallyReal_F
-- name    : Formalism.FrobeniusOrbits.Discr.totallyReal_F
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:12.768796+00:00
-- url     : https://prove2.me/theorems/3d0156e6-f8c9-48df-8510-523a1cff0ed4
-- title:
--   Discr: totally Real F
-- statement:
--   The Discr construction uses the totally Real F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L199-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L199-L210

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

theorem Formalism.FrobeniusOrbits.Discr.totallyReal_F (hz : IsPrimitiveRoot z (2 ^ (e + 2))) : IsTotallyReal ℚ⟮z + z⁻¹⟯ := by sorry
