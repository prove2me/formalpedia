-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_mk_lin_eq_iff
-- name    : Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.mk_lin_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:40.703657+00:00
-- url     : https://prove2.me/theorems/a4c1e38c-ec7b-4d89-92bd-2016a9f7162d
-- title:
--   unitary Absolute Value Bounds: mk lin eq iff
-- statement:
--   The unitary Absolute Value Bounds construction uses the mk lin eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/UnitaryDensityFieldTer.lean#L120-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/UnitaryDensityFieldTer.lean#L120-L151

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldBis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldTer
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
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {m : ℕ} (z : Fin m → ↥L) (g : Fin m → 𝓞 K)
variable {z g}

theorem Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.mk_lin_eq_iff (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (hzo : ∀ i j, i ≠ j → h (z i : V) (z j : V) = 0)
    (hzg : ∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i))
    (hg1 : ∀ i, g i - 1 ∈ extP K 𝔭 ^ k) (a b : Fin m → 𝓞 K) :
    (Submodule.Quotient.mk (lin z a) : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Submodule.Quotient.mk (lin z b) ↔ ∀ i, a i - b i ∈ extP K 𝔭 ^ k := by sorry
