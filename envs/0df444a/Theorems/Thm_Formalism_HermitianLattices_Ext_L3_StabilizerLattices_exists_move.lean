-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_exists_move
-- name    : Formalism.HermitianLattices.Ext.L3.StabilizerLattices.exists_move
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:58:56.695185+00:00
-- url     : https://prove2.me/theorems/dca9f870-2ca5-4495-b665-a5d6def81852
-- title:
--   Stabilizer Lattices: exists move
-- statement:
--   The Stabilizer Lattices construction uses the exists move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumOrbitsEquivariant.lean#L48-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumOrbitsEquivariant.lean#L48-L63

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

theorem Formalism.HermitianLattices.Ext.L3.StabilizerLattices.exists_move (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') (L : Submodule (𝓞 K) V) (p : Submodule (𝓞 K) V × V) :
    ∃ g : Formalism.HermitianLatticesTheory.isom h, p ∈ pairs h L (h S.x₀ S.x₀) →
      g • p = (Formalism.HermitianLatticesTheory.gmap g.1 p.1, S.x₀) ∧
      Formalism.HermitianLatticesTheory.gmap g.1 p.1 ∈ fibG S L (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)) := by sorry
