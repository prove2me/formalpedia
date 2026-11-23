-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_symm_apply
-- name    : Formalism.HermitianLattices.Ext.L3.SplitBAux.extOf_symm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:12.805632+00:00
-- url     : https://prove2.me/theorems/209c1c18-7a16-41d0-bff8-bbdb9c089c48
-- title:
--   Split BAux: ext Of symm apply
-- statement:
--   The Split BAux construction uses the ext Of symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean#L165-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean#L165-L166

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

theorem Formalism.HermitianLattices.Ext.L3.SplitBAux.extOf_symm_apply (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (c : K) (a : V') :
    (extOf S g').symm (c • S.x₀ + S.ι a) = c • S.x₀ + S.ι (g'.symm a) := by sorry
