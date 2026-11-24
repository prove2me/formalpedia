-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_alphaN_closed
-- name    : Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.alphaN_closed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:04.09588+00:00
-- url     : https://prove2.me/theorems/e9c37a94-eeab-48f8-a449-539e163eb969
-- title:
--   unitary Absolute Value Bounds: alpha N closed
-- statement:
--   The unitary Absolute Value Bounds construction uses the alpha N closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/UnitaryDensityFieldFurther.lean#L226-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/UnitaryDensityFieldFurther.lean#L226-L248

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

theorem Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.alphaN_closed (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) (hm : 1 ≤ finrank K V) :
    ∀ (v : ℕ) (n : 𝓞 F), n ≠ 0 → vF 𝔭 n = v → alphaN h L 𝔭 n =
      (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) *
        ∑ l ∈ Finset.range (v + 1),
          (etaF K F 𝔭 ^ finrank K V * ((Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V - 1))⁻¹) ^ l := by sorry
