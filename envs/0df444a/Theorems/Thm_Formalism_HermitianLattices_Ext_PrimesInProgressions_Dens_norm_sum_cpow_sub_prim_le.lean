-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_sum_cpow_sub_prim_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.norm_sum_cpow_sub_prim_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:30:15.034418+00:00
-- url     : https://prove2.me/theorems/9d111095-14e7-50f6-8ec8-6d793d54cc3d
-- title:
--   Dens: norm sum cpow sub prim le
-- statement:
--   The Dens construction uses the norm sum cpow sub prim le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensPair.lean#L183-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensPair.lean#L183-L204

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.norm_sum_cpow_sub_prim_le {U : ℕ} (hU : 1 ≤ U) {w : ℂ} (hw : 0 ≤ w.re) (hw1 : 1 - w ≠ 0)
    (V : ℕ) (hV : U ≤ V) :
    ‖∑ n ∈ Ioc U V, (n : ℂ) ^ (-w) - ((V : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w)‖ ≤
      ((V : ℝ) - U) * (‖w‖ / U) := by sorry
