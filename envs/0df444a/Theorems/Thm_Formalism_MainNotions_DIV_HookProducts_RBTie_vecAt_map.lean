-- Prove2me | Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_vecAt_map
-- name    : Formalism.MainNotions.DIV.HookProducts.RBTie.vecAt_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:09.02381+00:00
-- url     : https://prove2.me/theorems/c1faf5dc-f13b-4631-b0e6-69da27ca1d21
-- title:
--   RBTie: vec At map
-- statement:
--   The RBTie construction uses the vec At map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L16-L20

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.RBTie
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem Formalism.MainNotions.DIV.HookProducts.RBTie.vecAt_map (b : Basis ι K V) (b' : Basis κ K W) (v : InfinitePlace K) (u : V →ₗ[K] W) (x : V) :
    Formalism.HermitianLatticesTheory.vecAt b' v (u x) = (LinearMap.toMatrix b b' u).map v.embedding *ᵥ Formalism.HermitianLatticesTheory.vecAt b v x := by sorry
