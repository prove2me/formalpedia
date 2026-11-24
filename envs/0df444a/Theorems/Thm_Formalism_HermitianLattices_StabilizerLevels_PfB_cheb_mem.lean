-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_cheb_mem
-- name    : Formalism.HermitianLattices.StabilizerLevels.PfB.cheb_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:11:47.75997+00:00
-- url     : https://prove2.me/theorems/8754b641-ddfe-488b-8bc2-e60f017325f7
-- title:
--   Pf B: cheb mem
-- statement:
--   The Pf B construction uses the cheb mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L497-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L497-L511

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
open NumberField IntermediateField
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.HermitianLattices.StabilizerLevels.PfB.cheb_mem (hζ0 : ζ ≠ 0) (j : ℕ) : ζ ^ j + ζ⁻¹ ^ j ∈ F1 ζ ∧ ζ ^ (j + 1) + ζ⁻¹ ^ (j + 1) ∈ F1 ζ := by sorry
