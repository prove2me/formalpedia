-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_GramDeterminantPositive_exists_basis_of_ortho
-- name    : Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive.exists_basis_of_ortho
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:07.941775+00:00
-- url     : https://prove2.me/theorems/3780fc26-6e07-4b67-9ba9-9707ab9b6b8c
-- title:
--   Gram Determinant Positive: exists basis of ortho
-- statement:
--   The Gram Determinant Positive construction uses the exists basis of ortho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandG.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandG.lean#L24-L31

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandG
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
open Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive.exists_basis_of_ortho [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {k : ℕ}
    (v : Fin k → V) (hk : finrank K V = k) (ho : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (hne : ∀ i, h (v i) (v i) ≠ 0) : ∃ e : Basis (Fin k) K V, ∀ i, e i = v i := by sorry
