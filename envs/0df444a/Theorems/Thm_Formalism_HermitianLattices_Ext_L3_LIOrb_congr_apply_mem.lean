-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_congr_apply_mem
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.congr_apply_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:48:14.317799+00:00
-- url     : https://prove2.me/theorems/e9736830-0e1a-461a-930b-3b992674ee78
-- title:
--   LIOrb: congr apply mem
-- statement:
--   The LIOrb construction uses the congr apply mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ApplyMemSmulOfMemAutSub.lean#L109-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ApplyMemSmulOfMemAutSub.lean#L109-L127

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

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.congr_apply_mem {M₁ M₂ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {r₁ r₂ j : ℕ} (h1 : ((extP K 𝔭) ^ r₁ • locF 𝔭 M₁ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₂)
    (h2 : ((extP K 𝔭) ^ r₂ • locF 𝔭 M₂ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₁) (hj : r₂ + r₁ ≤ j)
    (g : V ≃ₗ[K] V)
    (hg : ∀ z ∈ locF 𝔭 M₁, g z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V))
    {z : V} (hz : z ∈ locF 𝔭 M₂) : g z ∈ locF 𝔭 M₂ := by sorry
