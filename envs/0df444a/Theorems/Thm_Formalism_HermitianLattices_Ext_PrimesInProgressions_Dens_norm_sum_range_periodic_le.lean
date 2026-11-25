-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_sum_range_periodic_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.norm_sum_range_periodic_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:22:13.142576+00:00
-- url     : https://prove2.me/theorems/2ef65795-4282-430e-82f5-41a2bd11e1f5
-- title:
--   Dens: norm sum range periodic le
-- statement:
--   The Dens construction uses the norm sum range periodic le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensPair.lean#L114-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensPair.lean#L114-L142

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.norm_sum_range_periodic_le {M : ℕ} [NeZero M] (h : ZMod M → ℂ) {K : ℝ} (hK : ∀ a, ‖h a‖ ≤ K)
    (h0 : ∑ a : ZMod M, h a = 0) (k : ℕ) : ‖∑ n ∈ range k, h (n : ZMod M)‖ ≤ K * M := by sorry
