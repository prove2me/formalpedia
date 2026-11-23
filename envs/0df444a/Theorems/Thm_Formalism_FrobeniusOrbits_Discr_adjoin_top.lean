-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Discr_adjoin_top
-- name    : Formalism.FrobeniusOrbits.Discr.adjoin_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:41.836267+00:00
-- url     : https://prove2.me/theorems/9c0f7acc-a89a-499a-a25c-309602aea7e2
-- title:
--   Discr: adjoin top
-- statement:
--   The Discr construction uses the adjoin top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L102-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L102-L111

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

theorem Formalism.FrobeniusOrbits.Discr.adjoin_top (hz : IsPrimitiveRoot z (2 ^ (e + 2))) :
    Algebra.adjoin ℚ⟮z + z⁻¹⟯ {z} = ⊤ := by sorry
