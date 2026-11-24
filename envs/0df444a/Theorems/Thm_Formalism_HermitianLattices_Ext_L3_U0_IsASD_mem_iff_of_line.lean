-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_mem_iff_of_line
-- name    : Formalism.HermitianLattices.Ext.L3.U0.IsASD.mem_iff_of_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:21.564813+00:00
-- url     : https://prove2.me/theorems/cace9192-eba8-424d-848a-b2930cb2bce4
-- title:
--   Is ASD: mem iff of line
-- statement:
--   The Is ASD construction uses the mem iff of line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthTransfer.lean#L94-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthTransfer.lean#L94-L110

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
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
open WA Module
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.U0.IsASD.mem_iff_of_line (hπ : IsUnif S π) {W : Submodule K V} {M : AddSubgroup V} {z : V}
    (hM : IsASD S π h W M z) (hline : ¬ ∃ ξ ∈ W, ξ ≠ 0 ∧ h z ξ = 0) :
    (∀ v ∈ W, v = (h z v * (h z z)⁻¹) • z) ∧ ∀ v, v ∈ M ↔ ∃ c ∈ S, v = c • z := by sorry
