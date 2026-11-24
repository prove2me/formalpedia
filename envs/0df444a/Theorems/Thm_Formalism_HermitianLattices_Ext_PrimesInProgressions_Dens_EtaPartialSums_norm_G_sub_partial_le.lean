-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_norm_G_sub_partial_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.norm_G_sub_partial_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:52.83471+00:00
-- url     : https://prove2.me/theorems/bac9a58a-3532-4289-beaa-5200eb1ec73a
-- title:
--   Eta Partial Sums: norm G sub partial le
-- statement:
--   The Eta Partial Sums construction uses the norm G sub partial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensLsA.lean#L231-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensLsA.lean#L231-L251

import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
open Formalism.FX.LFunctionPartialSum
variable (f : ℕ → ℂ)

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.norm_G_sub_partial_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖G f s - ∑ n ∈ Finset.Icc 1 N, f n * (n : ℂ) ^ (-s)‖ ≤
      B * (1 + ‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by sorry
