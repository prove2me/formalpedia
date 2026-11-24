-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_sqf_eq
-- name    : Formalism.HermitianLattices.StabilizerLevels.PfB.sqf_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:12:27.134787+00:00
-- url     : https://prove2.me/theorems/b4d849d2-0996-4a2f-b235-ff0aea389b24
-- title:
--   Pf B: sqf eq
-- statement:
--   The Pf B construction uses the sqf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L422-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L422-L448

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

theorem Formalism.HermitianLattices.StabilizerLevels.PfB.sqf_eq (m m' : ℤ) (hm : Squarefree m) (hm' : Squarefree m') (c : ℚ)
    (h : (m : ℚ) = c ^ 2 * m') : m = m' := by sorry
