-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_rpow_pos_exponent_bound
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.rpow_pos_exponent_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:18:36.817188+00:00
-- url     : https://prove2.me/theorems/c85923e4-1d79-55c0-bb4d-3edbde7f22b4
-- title:
--   Dens: rpow pos exponent bound
-- statement:
--   The Dens construction uses the rpow pos exponent bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/OneLeLogOfThreeLe.lean#L110-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/OneLeLogOfThreeLe.lean#L110-L130

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.rpow_pos_exponent_bound (q U : ℕ) (x σ : ℝ) (hx : 0 < x) (hqx : (q : ℝ) ≤ 2 * x) (hσ : 3 / 4 ≤ σ)
    (hσ1 : σ ≤ 1) (hU : U ≤ q ^ 12) : (U : ℝ) ^ (2 - 2 * σ) ≤ 64 * x ^ (24 * (1 - σ)) := by sorry
