-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_IA_relIndex_eq_of_map
-- name    : Formalism.HermitianLattices.Ext.L3.D2.IA.relIndex_eq_of_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:41.260491+00:00
-- url     : https://prove2.me/theorems/754f88d7-43ff-4fa5-9ed8-fb429b449867
-- title:
--   IA: rel Index eq of map
-- statement:
--   The IA construction uses the rel Index eq of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SurjectiveOfNondegenerate.lean#L10-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SurjectiveOfNondegenerate.lean#L10-L43

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SurjectiveOfNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2 Formalism.HermitianLattices.Ext.L3.D2.IA

theorem Formalism.HermitianLattices.Ext.L3.D2.IA.relIndex_eq_of_map {G M : Type*} [Group G] [AddCommGroup M] (H T : Subgroup G)
    (N' N : AddSubgroup M) (f : G → M) (hf : ∀ X ∈ T, f X ∈ N)
    (hc : ∀ X ∈ T, ∀ Y ∈ T, X⁻¹ * Y ∈ H ↔ f X - f Y ∈ N')
    (hsurj : ∀ Z ∈ N, ∃ X ∈ T, f X - Z ∈ N') : H.relIndex T = N'.relIndex N := by sorry
