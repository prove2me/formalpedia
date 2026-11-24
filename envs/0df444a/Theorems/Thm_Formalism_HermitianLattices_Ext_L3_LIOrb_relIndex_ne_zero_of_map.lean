-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_relIndex_ne_zero_of_map
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.relIndex_ne_zero_of_map
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:47:53.02888+00:00
-- url     : https://prove2.me/theorems/848b4053-7a41-4ba3-8f72-0fbf3b44773c
-- title:
--   LIOrb: rel Index ne zero of map
-- statement:
--   The LIOrb construction uses the rel Index ne zero of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ApplyMemSmulOfMemAutSub.lean#L175-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ApplyMemSmulOfMemAutSub.lean#L175-L189

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.relIndex_ne_zero_of_map {G X : Type*} [Group G] [Finite X] (H Γ : Subgroup G) (f : H → X)
    (hf : ∀ a b : H, f a = f b → (a : G)⁻¹ * b ∈ Γ) : Γ.relIndex H ≠ 0 := by sorry
