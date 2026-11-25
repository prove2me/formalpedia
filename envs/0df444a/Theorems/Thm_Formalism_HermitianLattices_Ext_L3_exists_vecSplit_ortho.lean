-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_vecSplit_ortho
-- name    : Formalism.HermitianLattices.Ext.L3.exists_vecSplit_ortho
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:19.037439+00:00
-- url     : https://prove2.me/theorems/900d66fa-d339-58af-88f3-366eaba1c9fb
-- title:
--   L3: exists vec Split ortho
-- statement:
--   The L3 construction uses the exists vec Split ortho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L371-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L371-L373

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

theorem Formalism.HermitianLattices.Ext.L3.exists_vecSplit_ortho {I : Submodule (𝓞 K) V} {I' : Submodule (𝓞 K) V'} {n : ℕ}
    (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I (n + 1)) (hI' : Formalism.HermitianLatticesTheory.IsOrthoLattice h' I' n) :
    ∃ S : VecSplit h h', h S.x₀ S.x₀ = 1 ∧ S.adjoin I' = I := by sorry
