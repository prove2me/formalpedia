-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_IA_exists_pow_smul
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.IA.exists_pow_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:29:57.104562+00:00
-- url     : https://prove2.me/theorems/4c080efe-f5d6-4492-bc6b-a656f5e23f83
-- title:
--   IA: exists pow smul
-- statement:
--   The IA construction uses the exists pow smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardEqRelIndex.lean#L35-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardEqRelIndex.lean#L35-L47

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardEqRelIndex
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb Formalism.HermitianLattices.Ext.L3.LIOrb.IA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.IA.exists_pow_smul {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {M N : Submodule (𝓞 K) V}
    (hM : Submodule.IsLattice K M) (hN : Submodule.IsLattice K N) :
    ∃ r : ℕ, ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, ι a • y ∈ locF 𝔭 N := by sorry
