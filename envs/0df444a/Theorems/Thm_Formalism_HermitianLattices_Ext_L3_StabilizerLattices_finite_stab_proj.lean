-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_finite_stab_proj
-- name    : Formalism.HermitianLattices.Ext.L3.StabilizerLattices.finite_stab_proj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:18.953582+00:00
-- url     : https://prove2.me/theorems/f169fdfd-b3fa-4937-8fc8-4bd80bc2aa38
-- title:
--   Stabilizer Lattices: finite stab proj
-- statement:
--   The Stabilizer Lattices construction uses the finite stab proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumOrbitsEquivariant.lean#L74-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumOrbitsEquivariant.lean#L74-L91

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsClassReps
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
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
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open Formalism.HermitianLattices.Ext.L3.StabilizerLattices
open SplitBAux

theorem Formalism.HermitianLattices.Ext.L3.StabilizerLattices.finite_stab_proj (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') (L : Submodule (𝓞 K) V) {p : Submodule (𝓞 K) V × V}
    (hp : p ∈ pairs h L (h S.x₀ S.x₀)) :
    (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (proj h p) : Set (Formalism.HermitianLatticesTheory.isom h)).Finite := by sorry
