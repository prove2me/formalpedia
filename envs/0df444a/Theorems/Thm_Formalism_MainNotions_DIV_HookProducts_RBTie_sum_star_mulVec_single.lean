-- Prove2me | Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_sum_star_mulVec_single
-- name    : Formalism.MainNotions.DIV.HookProducts.RBTie.sum_star_mulVec_single
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:54:11.41156+00:00
-- url     : https://prove2.me/theorems/c3ba6419-c3c3-4c95-860a-d9000a4910ad
-- title:
--   RBTie: sum star mul Vec single
-- statement:
--   The RBTie construction uses the sum star mul Vec single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L29-L31

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

theorem Formalism.MainNotions.DIV.HookProducts.RBTie.sum_star_mulVec_single {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (C : Matrix m n ℂ) (i j : n) :
    ∑ k, star ((C *ᵥ Pi.single i 1) k) * (C *ᵥ Pi.single j 1) k = (Cᴴ * C) i j := by sorry
