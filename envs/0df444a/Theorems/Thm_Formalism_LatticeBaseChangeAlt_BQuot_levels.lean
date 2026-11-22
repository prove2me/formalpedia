-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_levels
-- name    : Formalism.LatticeBaseChangeAlt.BQuot.levels
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:48.879971+00:00
-- url     : https://prove2.me/theorems/9e9d5e15-e215-4a7b-a661-785040cfc7fd
-- title:
--   BQuot: levels
-- statement:
--   The BQuot construction uses the levels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L99-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L99-L138

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.BQuot
variable {O V W : Type*} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]

theorem Formalism.LatticeBaseChangeAlt.BQuot.levels (N' M₁ N₁ Z Zm : Submodule O V) (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W)
    (hM : M₁ ≤ N') (hρ : ∀ x, ρ x ∈ AA')
    (hker : LinearMap.ker ρ = Zm.comap N'.subtype) (himg : (N₁.comap N'.subtype).map ρ = N₁') :
    ql M₁ (N₁ ⊔ Z) ≤ ql AA' AA + ql AA N₁' + ql Zm Z := by sorry
