-- Prove2me | Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_vecAt_std
-- name    : Formalism.MainNotions.DIV.HookProducts.RBTie.vecAt_std
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:40:39.397789+00:00
-- url     : https://prove2.me/theorems/93353fea-ee52-4047-9f92-fa354483b688
-- title:
--   RBTie: vec At std
-- statement:
--   The RBTie construction uses the vec At std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L22-L25

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

theorem Formalism.MainNotions.DIV.HookProducts.RBTie.vecAt_std {d : ℕ} (v : InfinitePlace K) (x : Fin d → K) :
    Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) v x = fun l => v.embedding (x l) := by sorry
