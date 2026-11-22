-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsLatIn_cut
-- name    : Formalism.HermitianLattices.Ext.L3.U0.IsLatIn.cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:49.566309+00:00
-- url     : https://prove2.me/theorems/6ad8181e-dffd-4c14-9a87-c73b43ec2777
-- title:
--   Is Lat In: cut
-- statement:
--   The Is Lat In construction uses the cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomScale.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomScale.lean#L37-L44

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

theorem Formalism.HermitianLattices.Ext.L3.U0.IsLatIn.cut (hM : IsLatIn S h W M) (X : V) : IsLatIn S h (cutW h W X) (cutM h M X) := by sorry
