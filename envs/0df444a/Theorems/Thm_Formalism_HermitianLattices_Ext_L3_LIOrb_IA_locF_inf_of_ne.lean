-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_IA_locF_inf_of_ne
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.IA.locF_inf_of_ne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:53:26.2694+00:00
-- url     : https://prove2.me/theorems/300c5dde-62e4-47b0-bb95-702c85ae5a5b
-- title:
--   IA: loc F inf of ne
-- statement:
--   The IA construction uses the loc F inf of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardEqRelIndex.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardEqRelIndex.lean#L63-L75

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

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.IA.locF_inf_of_ne {𝔭 𝔮 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (h𝔮 : 𝔮.IsMaximal) (hne : 𝔮 ≠ 𝔭)
    {M N : Submodule (𝓞 K) V} {r : ℕ} (hr : ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, ι a • y ∈ locF 𝔭 N) :
    locF 𝔮 (M ⊓ locF 𝔭 N) = locF 𝔮 M := by sorry
