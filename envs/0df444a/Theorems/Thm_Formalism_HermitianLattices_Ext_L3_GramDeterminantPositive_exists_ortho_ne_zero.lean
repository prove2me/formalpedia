-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_GramDeterminantPositive_exists_ortho_ne_zero
-- name    : Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive.exists_ortho_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:37:38.86163+00:00
-- url     : https://prove2.me/theorems/e8636786-b7c7-4fcb-8a6b-46707ccc1398
-- title:
--   Gram Determinant Positive: exists ortho ne zero
-- statement:
--   The Gram Determinant Positive construction uses the exists ortho ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandG.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandG.lean#L16-L22

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

theorem Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive.exists_ortho_ne_zero [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {k : ℕ}
    (v : Fin k → V) (hk : k < finrank K V) : ∃ x : V, x ≠ 0 ∧ ∀ i, h (v i) x = 0 := by sorry
