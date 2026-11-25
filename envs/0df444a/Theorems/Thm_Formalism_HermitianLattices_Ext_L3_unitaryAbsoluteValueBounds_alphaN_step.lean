-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_alphaN_step
-- name    : Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.alphaN_step
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:47:03.544893+00:00
-- url     : https://prove2.me/theorems/b9937b81-b9f8-5263-bf2a-01bd5e3c11c8
-- title:
--   unitary Absolute Value Bounds: alpha N step
-- statement:
--   The unitary Absolute Value Bounds construction uses the alpha N step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/UnitaryDensityFieldFurther.lean#L176-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/UnitaryDensityFieldFurther.lean#L176-L201

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldMore
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldFurther
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.alphaN_step (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ≠ 0) (hn𝔭 : n ∈ 𝔭) :
    alphaN h L 𝔭 n =
      (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) *
        (1 + etaF K F 𝔭 ^ finrank K V * ((Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V - 1))⁻¹) +
      (cntI hF 𝔭 (2 * vF 𝔭 n + 2) (finrank K V) (ι n) : ℝ) /
        (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * vF 𝔭 n + 2) * (2 * finrank K V - 1)) := by sorry
