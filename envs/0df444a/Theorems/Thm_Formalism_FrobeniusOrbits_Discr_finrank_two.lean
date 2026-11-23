-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Discr_finrank_two
-- name    : Formalism.FrobeniusOrbits.Discr.finrank_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:07:59.82503+00:00
-- url     : https://prove2.me/theorems/7233325b-706b-44f1-abd0-fb622e95f78a
-- title:
--   Discr: finrank two
-- statement:
--   The Discr construction uses the finrank two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L113-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L113-L126

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

theorem Formalism.FrobeniusOrbits.Discr.finrank_two (hz : IsPrimitiveRoot z (2 ^ (e + 2))) :
    Module.finrank ℚ⟮z + z⁻¹⟯ K = 2 := by sorry
