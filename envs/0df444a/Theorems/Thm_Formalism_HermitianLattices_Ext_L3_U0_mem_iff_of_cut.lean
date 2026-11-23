-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_iff_of_cut
-- name    : Formalism.HermitianLattices.Ext.L3.U0.mem_iff_of_cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:57.629656+00:00
-- url     : https://prove2.me/theorems/56528d91-ea29-45c6-8b36-3c55533a15d1
-- title:
--   U0: mem iff of cut
-- statement:
--   The U0 construction uses the mem iff of cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomScale.lean#L219-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomScale.lean#L219-L243

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

theorem Formalism.HermitianLattices.Ext.L3.U0.mem_iff_of_cut {W₁ W₂ : Submodule K V} {N : AddSubgroup V} (hM : IsLatIn S h W₁ M)
    (hN : IsLatIn S h W₂ N) {x X : V} (hx : x ∈ M) (hX : X ∈ N) (hu : IsUnitIn S (h x x))
    {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hgx : g x = X)
    (hcut : ∀ v, v ∈ cutM h M x ↔ g v ∈ cutM h N X) : ∀ v, v ∈ M ↔ g v ∈ N := by sorry
