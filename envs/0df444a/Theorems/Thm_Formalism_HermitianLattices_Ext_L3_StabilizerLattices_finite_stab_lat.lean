-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_finite_stab_lat
-- name    : Formalism.HermitianLattices.Ext.L3.StabilizerLattices.finite_stab_lat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:47:43.137169+00:00
-- url     : https://prove2.me/theorems/344c0e4f-df42-42c4-931c-672b04f33587
-- title:
--   Stabilizer Lattices: finite stab lat
-- statement:
--   The Stabilizer Lattices construction uses the finite stab lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsClassReps.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsClassReps.lean#L32-L37

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsClassReps
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
open Formalism.HermitianLattices.Ext.L3.StabilizerLattices
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.StabilizerLattices.finite_stab_lat (hs : h.IsSymm) (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V}
    (hM : Submodule.IsLattice K M) :
    (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) M : Set (Formalism.HermitianLatticesTheory.isom h)).Finite := by sorry
