-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_trace_pos_of_ortho
-- name    : Formalism.HermitianLattices.Ext.L3.trace_pos_of_ortho
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:45.308496+00:00
-- url     : https://prove2.me/theorems/d6ea9a8a-2991-4aa6-9812-c2ad07fbeeac
-- title:
--   L3: trace pos of ortho
-- statement:
--   The L3 construction uses the trace pos of ortho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FiniteDimensionalOfOrtho.lean#L114-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FiniteDimensionalOfOrtho.lean#L114-L129

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open StandardSymmetricSums

theorem Formalism.HermitianLattices.Ext.L3.trace_pos_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by sorry
