-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_cnt_tube_refine
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.cnt_tube_refine
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:17:52.3538+00:00
-- url     : https://prove2.me/theorems/f236f9eb-07f3-5889-ac06-6dfdee8d991a
-- title:
--   LIOrb: cnt tube refine
-- statement:
--   The LIOrb construction uses the cnt tube refine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulTopIff.lean#L221-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulTopIff.lean#L221-L253

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

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.cnt_tube_refine (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {x : V} (hxA : x ∈ locF 𝔭 A₀)
    (hx : h x x = algebraMap F K (n : F))
    {J : ℕ} (hJ : 4 * vF 𝔭 n + eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ J)
    {C : Subgroup (V ≃ₗ[K] V)} (hC : C ≤ autSub h (locF 𝔭 A₀))
    (hΓ : ∀ g ∈ autSub h (locF 𝔭 A₀), (∀ z ∈ locF 𝔭 A₀,
      g z - z ∈ ((extP K 𝔭) ^ (J - 2 * vF 𝔭 n) • locF 𝔭 A₀ : Submodule (𝓞 K) V)) → g ∈ C)
    {B : Submodule (𝓞 K) V} (hBA : B ≤ locF 𝔭 A₀) {r : ℕ}
    (hr : ((extP K 𝔭) ^ r • locF 𝔭 A₀ : Submodule (𝓞 K) V) ≤ B) {J₂ : ℕ} (hJ₂ : J ≤ J₂) :
    ∀ᶠ k in atTop, cnt h (locF 𝔭 A₀) 𝔭 k n (tube C (locF 𝔭 A₀) 𝔭 J x) =
      cnt h (locF 𝔭 A₀) 𝔭 k n (tube C B 𝔭 J₂ x) := by sorry
