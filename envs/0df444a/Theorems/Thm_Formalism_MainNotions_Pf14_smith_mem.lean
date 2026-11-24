-- Prove2me | Theorems.Thm_Formalism_MainNotions_Pf14_smith_mem
-- name    : Formalism.MainNotions.Pf14.smith_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:03:22.081385+00:00
-- url     : https://prove2.me/theorems/687daa53-6621-47b6-9f86-68b694a311e6
-- title:
--   Pf14: smith mem
-- statement:
--   The Pf14 construction uses the smith mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/DvdOfAdd.lean#L7-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/DvdOfAdd.lean#L7-L61

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ScaleEdges_DvdOfAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.Pf14
open Module

theorem Formalism.MainNotions.Pf14.smith_mem {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsLocalRing O]
    {I : Type*} [Fintype I] (S : Submodule O (I → O)) (a : O)
    (h : ∀ φ : I → O, (∃ i, IsUnit (φ i)) → ∃ s ∈ S, (∑ i, φ i * s i) ∣ a) (x : I → O) : a • x ∈ S := by sorry
