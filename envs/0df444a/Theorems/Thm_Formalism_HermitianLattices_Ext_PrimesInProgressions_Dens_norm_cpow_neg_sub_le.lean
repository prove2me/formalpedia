-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_cpow_neg_sub_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.norm_cpow_neg_sub_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:22:05.406908+00:00
-- url     : https://prove2.me/theorems/cc5620a7-1e52-4991-aad2-ea634491f307
-- title:
--   Dens: norm cpow neg sub le
-- statement:
--   The Dens construction uses the norm cpow neg sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensPair.lean#L12-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensPair.lean#L12-L42

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.norm_cpow_neg_sub_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(b : ℂ) ^ (-w) - (a : ℂ) ^ (-w)‖ ≤ ‖w‖ * ((b - a) / a) := by sorry
