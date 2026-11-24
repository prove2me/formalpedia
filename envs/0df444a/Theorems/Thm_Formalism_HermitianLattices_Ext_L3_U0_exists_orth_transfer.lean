-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_orth_transfer
-- name    : Formalism.HermitianLattices.Ext.L3.U0.exists_orth_transfer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:39.22886+00:00
-- url     : https://prove2.me/theorems/7681865d-fafc-4cfc-8d5a-d19c49503926
-- title:
--   U0: exists orth transfer
-- statement:
--   The U0 construction uses the exists orth transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthTransfer.lean#L62-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthTransfer.lean#L62-L87

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

theorem Formalism.HermitianLattices.Ext.L3.U0.exists_orth_transfer (hd : ∀ x, h x x = 0 → x = 0) {W₁ W₂ : Submodule K V}
    {ψ : V ≃ₗ[K] V} (hψ : ∀ a b, h (ψ a) (ψ b) = h a b) (hW : ∀ v ∈ W₁, ψ v ∈ W₂) {z₁ z₂ ξ : V}
    (hz₁ : z₁ ∈ W₁) (hz₁0 : z₁ ≠ 0) (hz₂ : z₂ ∈ W₂) (hz₂0 : z₂ ≠ 0) (hξ : ξ ∈ W₁) (hξ0 : ξ ≠ 0)
    (hzξ : h z₁ ξ = 0) : ∃ η ∈ W₂, η ≠ 0 ∧ h z₂ η = 0 := by sorry
