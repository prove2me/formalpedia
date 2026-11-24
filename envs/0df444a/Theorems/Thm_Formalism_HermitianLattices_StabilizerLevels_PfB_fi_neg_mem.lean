-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_fi_neg_mem
-- name    : Formalism.HermitianLattices.StabilizerLevels.PfB.fi_neg_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:12:37.989398+00:00
-- url     : https://prove2.me/theorems/0f3c8057-b98b-4d56-ab3a-5f9b23fcf81b
-- title:
--   Pf B: fi neg mem
-- statement:
--   The Pf B construction uses the fi neg mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L719-L721
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L719-L721

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField Ideal IsDedekindDomain nonZeroDivisors
open scoped Pointwise
variable {E : Type} [Field E] [NumberField E]

theorem Formalism.HermitianLattices.StabilizerLevels.PfB.fi_neg_mem {I : FractionalIdeal (𝓞 E)⁰ E} {x : E} (h : x ∈ I) : -x ∈ I := by sorry
