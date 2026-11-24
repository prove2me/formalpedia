-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_OrbSum_card_stab_sub
-- name    : Formalism.HermitianLattices.Ext.L3.OrbSum.card_stab_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:33.09552+00:00
-- url     : https://prove2.me/theorems/08d7a802-c0db-41eb-9ee6-08b3bbab23e9
-- title:
--   Orb Sum: card stab sub
-- statement:
--   The Orb Sum construction uses the card stab sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsRepsOfCover.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsRepsOfCover.lean#L54-L63

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.OrbSum
variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

theorem Formalism.HermitianLattices.Ext.L3.OrbSum.card_stab_sub (π : X → Y) (hπ : ∀ (g : G) x, π (g • x) = g • π x) (x : X) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer G (π x)) x) =
      Nat.card (MulAction.stabilizer G x) := by sorry
