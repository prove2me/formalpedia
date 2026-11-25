-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_cnt_tube_eq
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.cnt_tube_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:16:20.362419+00:00
-- url     : https://prove2.me/theorems/1df7b380-87e1-5bfe-89d9-80ff333c4916
-- title:
--   LIOrb: cnt tube eq
-- statement:
--   The LIOrb construction uses the cnt tube eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulTopIff.lean#L105-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulTopIff.lean#L105-L182

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotInfNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomCongr
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeVdLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralAtLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulTopIff
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

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.cnt_tube_eq {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (n : 𝓞 F) {x : V} (hxA : x ∈ locF 𝔭 A₀)
    {J k : ℕ} (hJk : J ≤ k) {D : Subgroup (V ≃ₗ[K] V)} (hD : D ≤ autSub h (locF 𝔭 A₀)) :
    cnt h (locF 𝔭 A₀) 𝔭 k n (tube D (locF 𝔭 A₀) 𝔭 J x) =
      (stabB h (locF 𝔭 A₀) 𝔭 J x).relIndex D * cnt h (locF 𝔭 A₀) 𝔭 k n (tube ⊥ (locF 𝔭 A₀) 𝔭 J x) := by sorry
