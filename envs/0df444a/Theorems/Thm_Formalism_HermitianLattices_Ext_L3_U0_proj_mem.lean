-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_proj_mem
-- name    : Formalism.HermitianLattices.Ext.L3.U0.proj_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:58.447176+00:00
-- url     : https://prove2.me/theorems/260ed3ec-7b2e-4821-88b5-e80bc36813a9
-- title:
--   U0: proj mem
-- statement:
--   The U0 construction uses the proj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomScale.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomScale.lean#L30-L35

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
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

theorem Formalism.HermitianLattices.Ext.L3.U0.proj_mem (hM : IsLatIn S h W M) {X : V} (hX : X ∈ M) (hu : IsUnitIn S (h X X)) {m : V}
    (hm : m ∈ M) : m - (h X m * (h X X)⁻¹) • X ∈ cutM h M X := by sorry
