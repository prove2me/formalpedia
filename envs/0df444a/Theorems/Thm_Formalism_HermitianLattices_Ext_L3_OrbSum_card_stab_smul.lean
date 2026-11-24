-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_OrbSum_card_stab_smul
-- name    : Formalism.HermitianLattices.Ext.L3.OrbSum.card_stab_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:26.153387+00:00
-- url     : https://prove2.me/theorems/8032af34-483a-4eb6-a5b3-2f8d08e08c0a
-- title:
--   Orb Sum: card stab smul
-- statement:
--   The Orb Sum construction uses the card stab smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsRepsOfCover.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsRepsOfCover.lean#L49-L52

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

theorem Formalism.HermitianLattices.Ext.L3.OrbSum.card_stab_smul (g : G) (x : X) :
    Nat.card (MulAction.stabilizer G (g • x)) = Nat.card (MulAction.stabilizer G x) := by sorry
