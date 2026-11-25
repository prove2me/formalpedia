-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_sum_twist_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.norm_sum_twist_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:44:24.564029+00:00
-- url     : https://prove2.me/theorems/06dc4973-801f-5ef2-ae1a-f1599506d01a
-- title:
--   Dens: norm sum twist le
-- statement:
--   The Dens construction uses the norm sum twist le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensPair.lean#L66-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensPair.lean#L66-L104

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.norm_sum_twist_le (g : ℕ → ℂ) {m : ℝ} (hGs : ∀ k, ‖∑ i ∈ range k, g i‖ ≤ m) {w : ℂ}
    (hw : 0 ≤ w.re) {U : ℕ} (hU : 1 ≤ U) :
    ‖∑ n ∈ Ioc U (2 * U), g n * (n : ℂ) ^ (-w)‖ ≤ 2 * m * (1 + ‖w‖) := by sorry
