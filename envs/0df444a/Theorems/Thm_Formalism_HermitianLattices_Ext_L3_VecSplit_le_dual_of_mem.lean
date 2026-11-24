-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_le_dual_of_mem
-- name    : Formalism.HermitianLattices.Ext.L3.VecSplit.le_dual_of_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:21.6448+00:00
-- url     : https://prove2.me/theorems/4b349d7e-f09e-42f3-94e4-c4b9aa580189
-- title:
--   Vec Split: le dual of mem
-- statement:
--   The Vec Split construction uses the le dual of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsVecOfHermRep.lean#L103-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsVecOfHermRep.lean#L103-L112

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
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

theorem Formalism.HermitianLattices.Ext.L3.VecSplit.le_dual_of_mem {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (hs : h.IsSymm) (S : VecSplit h h') {Λ : Submodule (𝓞 K) V}
    (hΛ : Formalism.HermitianLatticesTheory.IsIntegralLat h Λ) (hx : S.x₀ ∈ Λ) :
    S.adjoin (S.cut Λ) ≤ Λ ∧ Λ ≤ Formalism.HermitianLatticesTheory.dual h (S.adjoin (S.cut Λ)) := by sorry
