-- Prove2me | Theorems.Thm_Formalism_L2_G_mem_span_of_card
-- name    : Formalism.L2.G.mem_span_of_card
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:34:00.482354+00:00
-- url     : https://prove2.me/theorems/d689df4e-e538-4b4a-8177-df46c2d6fc4f
-- title:
--   G: mem span of card
-- statement:
--   The G construction uses the mem span of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TiedFamilies/TieDim.lean#L23-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TiedFamilies/TieDim.lean#L23-L42

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

theorem Formalism.L2.G.mem_span_of_card {O Kf W ι : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W] (M : Submodule O W) [Module.Finite O M]
    [Fintype ι] (c : ι → W) (hli : LinearIndependent Kf c) (hc : ∀ i, c i ∈ Submodule.span Kf (M : Set W))
    (hcard : Fintype.card ι = Module.finrank O M) (F : W) (hF : F ∈ M) : F ∈ Submodule.span Kf (Set.range c) := by sorry
