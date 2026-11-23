-- Prove2me | Theorems.Thm_Formalism_MainNotions_Pf14_dvd_of_add
-- name    : Formalism.MainNotions.Pf14.dvd_of_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:16.083865+00:00
-- url     : https://prove2.me/theorems/e328ff3e-d290-4c53-95d7-5339ae053df5
-- title:
--   Pf14: dvd of add
-- statement:
--   The Pf14 construction uses the dvd of add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/DvdOfAdd.lean#L63-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/DvdOfAdd.lean#L63-L77

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

theorem Formalism.MainNotions.Pf14.dvd_of_add {O : Type*} [CommRing O] [IsLocalRing O] (π : O) (hπ : ¬ IsUnit π) (D : ℕ) (a z : O)
    (ha : a ∣ π ^ D) : (a + π ^ (D + 1) * z) ∣ π ^ D := by sorry
