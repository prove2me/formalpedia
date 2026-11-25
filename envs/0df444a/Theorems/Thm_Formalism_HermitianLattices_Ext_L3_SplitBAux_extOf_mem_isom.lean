-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_mem_isom
-- name    : Formalism.HermitianLattices.Ext.L3.SplitBAux.extOf_mem_isom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:49:16.205359+00:00
-- url     : https://prove2.me/theorems/55fb60a0-bfbb-48d0-bf7e-16075022a323
-- title:
--   Split BAux: ext Of mem isom
-- statement:
--   The Split BAux construction uses the ext Of mem isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean#L177-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean#L177-L184

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

theorem Formalism.HermitianLattices.Ext.L3.SplitBAux.extOf_mem_isom (hs : h.IsSymm) (S : VecSplit h h') {g' : V' ≃ₗ[K] V'}
    (hg : g' ∈ Formalism.HermitianLatticesTheory.isom h') : extOf S g' ∈ Formalism.HermitianLatticesTheory.isom h := by sorry
