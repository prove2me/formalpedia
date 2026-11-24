-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_res_symm_spec
-- name    : Formalism.HermitianLattices.Ext.L3.SplitBAux.res_symm_spec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:41.763817+00:00
-- url     : https://prove2.me/theorems/0130c6c0-b96b-4bed-82f6-a0d407792e52
-- title:
--   Split BAux: res symm spec
-- statement:
--   The Split BAux construction uses the res symm spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean#L117-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean#L117-L119

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
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
open Formalism.HermitianLattices.Ext.L3.SplitBAux
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.SplitBAux.res_symm_spec (S : VecSplit h h') (g : V ≃ₗ[K] V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) (a : V') : S.ι ((res S g hg hx).symm a) = g.symm (S.ι a) := by sorry
