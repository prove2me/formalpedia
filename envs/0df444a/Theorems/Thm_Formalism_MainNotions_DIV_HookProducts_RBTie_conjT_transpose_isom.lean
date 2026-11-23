-- Prove2me | Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_conjT_transpose_isom
-- name    : Formalism.MainNotions.DIV.HookProducts.RBTie.conjT_transpose_isom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:40:55.563917+00:00
-- url     : https://prove2.me/theorems/1117362d-da8d-4213-a30b-2635a4448271
-- title:
--   RBTie: conj T transpose isom
-- statement:
--   The RBTie construction uses the conj T transpose isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieOp.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieOp.lean#L26-L30

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieOp
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
  {VN VR : Type} [AddCommGroup VN] [Module K VN] [AddCommGroup VR] [Module K VR]
  {ιN ιR : Type} [Fintype ιN] [DecidableEq ιN] [Fintype ιR] [DecidableEq ιR] {d n : ℕ}

theorem Formalism.MainNotions.DIV.HookProducts.RBTie.conjT_transpose_isom {ι κ : Type} [Fintype ι] [Fintype κ] (U : Matrix ι κ ℂ) : ((Uᴴ)ᵀ)ᴴ * (Uᴴ)ᵀ = (Uᴴ * U)ᵀ := by sorry
