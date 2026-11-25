-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_isOrthoLattice_adjoin
-- name    : Formalism.HermitianLattices.Ext.L3.VecSplit.isOrthoLattice_adjoin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:17.733518+00:00
-- url     : https://prove2.me/theorems/b64d981e-f523-5bcf-842f-1c4e2e63bd76
-- title:
--   Vec Split: is Ortho Lattice adjoin
-- statement:
--   The Vec Split construction uses the is Ortho Lattice adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L375-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L375-L377

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.VecSplit.isOrthoLattice_adjoin (hs : h.IsSymm) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1)
    {I' : Submodule (𝓞 K) V'} {n : ℕ} (hI' : Formalism.HermitianLatticesTheory.IsOrthoLattice h' I' n) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice h (S.adjoin I') (n + 1) := by sorry
