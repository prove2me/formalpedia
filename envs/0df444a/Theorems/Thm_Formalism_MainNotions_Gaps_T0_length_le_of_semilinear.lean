-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_length_le_of_semilinear
-- name    : Formalism.MainNotions.Gaps.T0.length_le_of_semilinear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:39.502619+00:00
-- url     : https://prove2.me/theorems/74267d43-b174-48b1-bb97-f8fab4c2ca63
-- title:
--   T0: length le of semilinear
-- statement:
--   The T0 construction uses the length le of semilinear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LengthLeOfSemilinear.lean#L298-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LengthLeOfSemilinear.lean#L298-L316

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
open Module Formalism.LatticeBaseChangeAlt Formalism.LatticeBaseChangeAlt.BQuot
variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
  [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']

theorem Formalism.MainNotions.Gaps.T0.length_le_of_semilinear {Q Q' : Type} [AddCommGroup Q] [Module O Q] [AddCommGroup Q']
    [Module O' Q'] (ϖ : O) (hϖ : Irreducible ϖ) (hϖ' : Irreducible (algebraMap O O' ϖ))
    (g : Q →ₛₗ[algebraMap O O'] Q') (hg : Submodule.span O' (Set.range g) = ⊤) :
    Module.length O' Q' ≤ Module.length O Q := by sorry
