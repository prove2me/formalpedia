-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_rpow_neg_exponent_bound
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.rpow_neg_exponent_bound
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:55:38.974048+00:00
-- url     : https://prove2.me/theorems/48de75d6-9bdb-4493-9da6-d7528ff141bd
-- title:
--   Dens: rpow neg exponent bound
-- statement:
--   The Dens construction uses the rpow neg exponent bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/OneLeLogOfThreeLe.lean#L94-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/OneLeLogOfThreeLe.lean#L94-L108

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_OneLeLogOfThreeLe
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.rpow_neg_exponent_bound (q U : ℕ) (σ : ℝ) (hq : 1 ≤ q) (hσ : 3 / 4 ≤ σ) (hU : q ^ 3 ≤ U) :
    (U : ℝ) ^ (1 - 2 * σ) ≤ 1 / ((q : ℝ) * Real.sqrt q) := by sorry
