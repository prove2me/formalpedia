-- Prove2me | Theorems.Thm_Formalism_L2_G_finrank_span_le
-- name    : Formalism.L2.G.finrank_span_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:21.723128+00:00
-- url     : https://prove2.me/theorems/56782e24-5915-4eb2-9c24-5880cc1b1239
-- title:
--   G: finrank span le
-- statement:
--   The G construction uses the finrank span le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TiedFamilies/TieDim.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TiedFamilies/TieDim.lean#L7-L21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TiedFamilies_TieDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.G
open Module

theorem Formalism.L2.G.finrank_span_le {O Kf W : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W] (M : Submodule O W) [Module.Finite O M] :
    Module.rank Kf (Submodule.span Kf (M : Set W)) ≤ (Module.finrank O M : Cardinal) := by sorry
