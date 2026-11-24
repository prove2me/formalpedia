-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_asd_base
-- name    : Formalism.HermitianLattices.Ext.L3.U0.asd_base
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:25.722778+00:00
-- url     : https://prove2.me/theorems/527d94c6-584c-4571-8151-c6d05f108b66
-- title:
--   U0: asd base
-- statement:
--   The U0 construction uses the asd base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthTransfer.lean#L112-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthTransfer.lean#L112-L159

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

theorem Formalism.HermitianLattices.Ext.L3.U0.asd_base (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    {W₁ W₂ : Submodule K V} {M N : AddSubgroup V} {z₁ z₂ : V} {φ : V ≃ₗ[K] V}
    (hM : IsASD S π h W₁ M z₁) (hN : IsASD S π h W₂ N z₂) (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h)
    (hW : ∀ v, v ∈ W₁ ↔ φ v ∈ W₂) (h1 : ¬ ∃ ξ ∈ W₁, ξ ≠ 0 ∧ h z₁ ξ = 0)
    (h2 : ¬ ∃ ξ ∈ W₂, ξ ≠ 0 ∧ h z₂ ξ = 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by sorry
