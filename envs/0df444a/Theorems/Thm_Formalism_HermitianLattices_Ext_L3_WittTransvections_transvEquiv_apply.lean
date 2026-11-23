-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WittTransvections_transvEquiv_apply
-- name    : Formalism.HermitianLattices.Ext.L3.WittTransvections.transvEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:51.223972+00:00
-- url     : https://prove2.me/theorems/b3cb3a69-a5d3-488e-ae89-b50f81996bfe
-- title:
--   Witt Transvections: transv Equiv apply
-- statement:
--   The Witt Transvections construction uses the transv Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomMapOfEq.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomMapOfEq.lean#L35-L37

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq
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
open Formalism.HermitianLattices.Ext.L3.WittTransvections
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem Formalism.HermitianLattices.Ext.L3.WittTransvections.transvEquiv_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {ξ : K}
    (hξ : ξ + star ξ = ξ * star ξ * h u u) (v : V) :
    transvEquiv h u hξ v = v - (ξ * h u v) • u := by sorry
