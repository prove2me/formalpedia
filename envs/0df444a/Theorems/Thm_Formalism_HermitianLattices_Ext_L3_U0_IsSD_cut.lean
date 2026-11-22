-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_cut
-- name    : Formalism.HermitianLattices.Ext.L3.U0.IsSD.cut
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:05.637793+00:00
-- url     : https://prove2.me/theorems/ca067aed-6245-4db8-873e-9e02335cf5f5
-- title:
--   Is SD: cut
-- statement:
--   The Is SD construction uses the cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomScale.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomScale.lean#L54-L58

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

theorem Formalism.HermitianLattices.Ext.L3.U0.IsSD.cut (hM : IsSD S h W M) {X : V} (hX : X ∈ M) (hu : IsUnitIn S (h X X)) :
    IsSD S h (cutW h W X) (cutM h M X) := by sorry
