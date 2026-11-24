-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_ql_span_le
-- name    : Formalism.MainNotions.Gaps.T0.ql_span_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:03.332084+00:00
-- url     : https://prove2.me/theorems/ce4da3a0-fc07-4765-83c6-c62c2ed4625e
-- title:
--   T0: ql span le
-- statement:
--   The T0 construction uses the ql span le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LengthLeOfSemilinear.lean#L318-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LengthLeOfSemilinear.lean#L318-L344

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

theorem Formalism.MainNotions.Gaps.T0.ql_span_le {V V₁ : Type} [AddCommGroup V] [Module O V] [AddCommGroup V₁] [Module O' V₁]
    (ϖ : O) (hϖ : Irreducible ϖ) (hϖ' : Irreducible (algebraMap O O' ϖ))
    (jj : V →ₛₗ[algebraMap O O'] V₁) (A S : Submodule O V) (S₁ : Submodule O' V₁)
    (h : ∀ x ∈ S, jj x ∈ S₁) :
    ql (Submodule.span O' (jj '' (A : Set V))) S₁ ≤ ql A S := by sorry
