-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_alphaN_of_vd_zero_unit
-- name    : Formalism.HermitianLattices.Ext.L3.alphaN_of_vd_zero_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:36.24655+00:00
-- url     : https://prove2.me/theorems/c3d02425-93ad-4a34-af2a-e9e8e2fc42ad
-- title:
--   L3: alpha N of vd zero unit
-- statement:
--   The L3 construction uses the alpha N of vd zero unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlphaNOfVdZeroUnit.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlphaNOfVdZeroUnit.lean#L83-L88

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldFurther
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaNOfVdZeroUnit
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.alphaN_of_vd_zero_unit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0)
    (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ∉ 𝔭) :
    alphaN h L 𝔭 n = (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) := by sorry
