-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_IA_vd_mul
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.IA.vd_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:47:30.293679+00:00
-- url     : https://prove2.me/theorems/0cbb3e18-b804-49b6-b471-5dc65ab5c619
-- title:
--   IA: vd mul
-- statement:
--   The IA construction uses the vd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardEqRelIndex.lean#L137-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardEqRelIndex.lean#L137-L190

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

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.IA.vd_mul {𝔭 : Ideal (𝓞 F)} (hF : IsFixF K F) [FiniteDimensional K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {M N : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) (hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M)
    (hN : Submodule.IsLattice K N) (h𝔭 : 𝔭.IsMaximal) :
    (M ⊓ locF 𝔭 N).toAddSubgroup.relIndex M.toAddSubgroup * Ideal.absNorm 𝔭 ^ vd h M 𝔭 =
      Ideal.absNorm 𝔭 ^ vd h (M ⊓ locF 𝔭 N) 𝔭 := by sorry
