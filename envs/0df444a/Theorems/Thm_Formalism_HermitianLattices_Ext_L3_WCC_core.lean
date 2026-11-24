-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCC_core
-- name    : Formalism.HermitianLattices.Ext.L3.WCC.core
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:31:45.240741+00:00
-- url     : https://prove2.me/theorems/0d51f920-cd1a-41ce-9f92-e758d7f32cbb
-- title:
--   WCC: core
-- statement:
--   The WCC construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/WCC.lean#L18-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/WCC.lean#L18-L155

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LaurentAdjoinEqOfImageEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_WCC
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WCC
open WCA WCB
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

theorem Formalism.HermitianLattices.Ext.L3.WCC.core (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (han : ∀ x, h x x = 0 → x = 0) {A : Submodule (𝓞 K) V} (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {v : ℕ} (hv : n ∉ 𝔭 ^ (v + 1))
    {x y : V} (hx : InL 𝔭 A 0 x) (hxx : h x x = κ (ι n)) (hyy : h y y = κ (ι n)) {J : ℕ}
    (hJ : 1 ≤ J) (hw : InL 𝔭 A (v + (v + J)) (y - x)) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ z, InL 𝔭 A 0 z → InL 𝔭 A J (g z - z)) ∧
      (∀ z, InL 𝔭 A 0 z → InL 𝔭 A 0 (g.symm z)) ∧ g x = y := by sorry
