-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_log_pow_five_le_sqrt
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.log_pow_five_le_sqrt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:44:14.085843+00:00
-- url     : https://prove2.me/theorems/420c4da6-8085-4180-b248-98f22cf394ab
-- title:
--   Dens: log pow five le sqrt
-- statement:
--   The Dens construction uses the log pow five le sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/DyadicSizeLePowTwelveSecond.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/DyadicSizeLePowTwelveSecond.lean#L9-L26

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DyadicSizeLePowTwelveSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.log_pow_five_le_sqrt (c : ℝ) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → c * Real.log q ^ 5 ≤ Real.sqrt q := by sorry
