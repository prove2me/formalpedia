-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_unit_norm
-- name    : Formalism.HermitianLattices.Ext.L3.U0.exists_unit_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:00.818564+00:00
-- url     : https://prove2.me/theorems/acb501a2-5e01-4f80-aacf-721449a4628b
-- title:
--   U0: exists unit norm
-- statement:
--   The U0 construction uses the exists unit norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean#L171-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean#L171-L191

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

theorem Formalism.HermitianLattices.Ext.L3.U0.exists_unit_norm (hS : IsHermSemilocal S) (hπ : IsUnif S π) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {M : AddSubgroup V} (hM : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M)
    (hint : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ S) {y w : V} (hy : y ∈ M) (hw : w ∈ M)
    (hn : ¬ Dv S π (h w y)) : ∃ x ∈ M, IsUnitIn S (h x x) := by sorry
