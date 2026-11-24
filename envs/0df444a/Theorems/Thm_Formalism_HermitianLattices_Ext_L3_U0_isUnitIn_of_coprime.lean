-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_isUnitIn_of_coprime
-- name    : Formalism.HermitianLattices.Ext.L3.U0.isUnitIn_of_coprime
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:47.339838+00:00
-- url     : https://prove2.me/theorems/3f5c36a9-6910-4aec-abaf-5f61b42e3faf
-- title:
--   U0: is Unit In of coprime
-- statement:
--   The U0 construction uses the is Unit In of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsPrimitiveNorm.lean#L178-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsPrimitiveNorm.lean#L178-L218

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
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
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}

theorem Formalism.HermitianLattices.Ext.L3.U0.isUnitIn_of_coprime (hS : IsHermSemilocal S) (hπ : IsUnif S π) {t : K} (ht : t ∈ S)
    (hc : ∀ d : K, d ≠ 0 → t * d⁻¹ ∈ S → π * d⁻¹ ∈ S → d⁻¹ ∈ S) : IsUnitIn S t := by sorry
