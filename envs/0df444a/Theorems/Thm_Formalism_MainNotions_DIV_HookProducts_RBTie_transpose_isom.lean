-- Prove2me | Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_transpose_isom
-- name    : Formalism.MainNotions.DIV.HookProducts.RBTie.transpose_isom
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:54:55.37599+00:00
-- url     : https://prove2.me/theorems/66ea5814-1d19-46af-8fe3-0b8ce3178643
-- title:
--   RBTie: transpose isom
-- statement:
--   The RBTie construction uses the transpose isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieOp.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieOp.lean#L22-L24

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

theorem Formalism.MainNotions.DIV.HookProducts.RBTie.transpose_isom {ι κ : Type} [Fintype ι] [Fintype κ] (U : Matrix ι κ ℂ) : (Uᵀ)ᴴ * Uᵀ = (U * Uᴴ)ᵀ := by sorry
