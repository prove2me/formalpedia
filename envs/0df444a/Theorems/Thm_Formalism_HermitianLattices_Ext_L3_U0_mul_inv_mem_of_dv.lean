-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mul_inv_mem_of_dv
-- name    : Formalism.HermitianLattices.Ext.L3.U0.mul_inv_mem_of_dv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:37:11.684199+00:00
-- url     : https://prove2.me/theorems/2b3f5a95-53fd-41bd-9586-b26c31517e45
-- title:
--   U0: mul inv mem of dv
-- statement:
--   The U0 construction uses the mul inv mem of dv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsPrimitiveNorm.lean#L142-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsPrimitiveNorm.lean#L142-L151

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

theorem Formalism.HermitianLattices.Ext.L3.U0.mul_inv_mem_of_dv (hπ : IsUnif S π) {a b : K} (ha : Dv S π a)
    (hb : IsUnitIn S (b * π⁻¹)) : a * b⁻¹ ∈ S := by sorry
