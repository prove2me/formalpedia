-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_roL_diff
-- name    : Formalism.HermitianLattices.Ext.L3.A5.roL_diff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:15:50.110403+00:00
-- url     : https://prove2.me/theorems/357ac278-dc7e-5027-9347-afd10d0e1187
-- title:
--   A5: ro L diff
-- statement:
--   The A5 construction uses the ro L diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ALocEqRoL.lean#L61-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ALocEqRoL.lean#L61-L93

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemBoxSet
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ALocEqRoL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
  {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
  (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
  {S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}}
  (hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S)
include hK hF hs hd hL hLi hS
include hm

theorem Formalism.HermitianLattices.Ext.L3.A5.roL_diff (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (j : ℕ) :
    |roL h L S 𝔭 (j + 1) - roL h L S 𝔭 j| ≤
      8 * ((j : ℝ) + 2) ^ 2 / (Ideal.absNorm 𝔭.1 : ℝ) := by sorry
