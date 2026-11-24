-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_norm_of_orth
-- name    : Formalism.HermitianLattices.Ext.L3.U0.exists_norm_of_orth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:27.35487+00:00
-- url     : https://prove2.me/theorems/dab3f478-4729-4e20-a26d-4e7c1fc554bd
-- title:
--   U0: exists norm of orth
-- statement:
--   The U0 construction uses the exists norm of orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean#L249-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean#L249-L287

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K} {π : K}
variable {V : Type*} [AddCommGroup V] [Module K V]

theorem Formalism.HermitianLattices.Ext.L3.U0.exists_norm_of_orth (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {M : AddSubgroup V}
    (hM : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M) {y w : V}
    (hy : y ∈ M) (hw : w ∈ M) {a u : K} (ha : a ∈ S) (hu : IsUnitIn S u) (huf : star u = u)
    (hyy : h y y = star a * a * u) (hna : ¬ Dv S π a) (hN : Dv S π (star a * a))
    (hwy : h w y = 0) (hww : IsUnitIn S (h w w)) : ∃ X ∈ M, h X X = u := by sorry
