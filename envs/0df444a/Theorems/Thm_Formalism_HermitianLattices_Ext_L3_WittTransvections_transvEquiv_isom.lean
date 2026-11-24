-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WittTransvections_transvEquiv_isom
-- name    : Formalism.HermitianLattices.Ext.L3.WittTransvections.transvEquiv_isom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:45.290205+00:00
-- url     : https://prove2.me/theorems/a5c02885-d50e-47ba-b04d-d28c97ca2903
-- title:
--   Witt Transvections: transv Equiv isom
-- statement:
--   The Witt Transvections construction uses the transv Equiv isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomMapOfEq.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomMapOfEq.lean#L39-L46

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

theorem Formalism.HermitianLattices.Ext.L3.WittTransvections.transvEquiv_isom {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u : V) {ξ : K}
    (hξ : ξ + star ξ = ξ * star ξ * h u u) (v w : V) :
    h (transvEquiv h u hξ v) (transvEquiv h u hξ w) = h v w := by sorry
