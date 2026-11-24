-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_ncard_orb
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.ncard_orb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:07.389909+00:00
-- url     : https://prove2.me/theorems/d574e370-216a-4e83-a49d-071210896473
-- title:
--   LIOrb: ncard orb
-- statement:
--   The LIOrb construction uses the ncard orb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqOfCover.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqOfCover.lean#L102-L105

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
open Subgroup
variable {G : Type*} [Group G]

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.ncard_orb {X Y : Type*} [MulAction G X] [MulAction G Y] (t : X) (y : Y) :
    {x : X | ∃ g : G, g • y = y ∧ g • t = x}.ncard =
      (MulAction.stabilizer G t).relIndex (MulAction.stabilizer G y) := by sorry
