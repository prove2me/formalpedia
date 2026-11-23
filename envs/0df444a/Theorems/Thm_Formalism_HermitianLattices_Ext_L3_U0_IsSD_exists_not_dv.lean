-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_exists_not_dv
-- name    : Formalism.HermitianLattices.Ext.L3.U0.IsSD.exists_not_dv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:14:05.472467+00:00
-- url     : https://prove2.me/theorems/f31622d9-f880-4b3b-898c-2f8acafb6f4c
-- title:
--   Is SD: exists not dv
-- statement:
--   The Is SD construction uses the exists not dv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsPrimitiveNorm.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsPrimitiveNorm.lean#L89-L96

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

theorem Formalism.HermitianLattices.Ext.L3.U0.IsSD.exists_not_dv (hπ : IsUnif S π) (hM : IsSD S h W M) {y : V} (hy : y ∈ M)
    (hprim : ∀ c : K, c • y ∈ M → c ∈ S) : ∃ w ∈ M, ¬ Dv S π (h w y) := by sorry
