-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_exists_norm_one_of_pair
-- name    : Formalism.HermitianLattices.Ext.L3.WA.exists_norm_one_of_pair
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:44.0569+00:00
-- url     : https://prove2.me/theorems/530a4fad-d181-4632-8414-ae00bcf8be91
-- title:
--   WA: exists norm one of pair
-- statement:
--   The WA construction uses the exists norm one of pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormOneOfPair.lean#L77-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormOneOfPair.lean#L77-L134

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K}
variable {V : Type*} [AddCommGroup V] [Module K V]

theorem Formalism.HermitianLattices.Ext.L3.WA.exists_norm_one_of_pair (hS : IsHermSemilocal S) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {y w : V} {a : K} (ha : a ∈ S) (ha0 : a ≠ 0) (hy : h y y = star a * a) (hyw : h y w = 1)
    (hw : h w w ∈ S) :
    ∃ c ∈ S, ∃ d ∈ S, h (c • w + d • y) (c • w + d • y) = 1 := by sorry
