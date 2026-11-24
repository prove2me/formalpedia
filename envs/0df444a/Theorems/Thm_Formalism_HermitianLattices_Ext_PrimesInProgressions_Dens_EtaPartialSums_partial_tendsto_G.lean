-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_partial_tendsto_G
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.partial_tendsto_G
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:52.870131+00:00
-- url     : https://prove2.me/theorems/4f80d027-7711-4ad2-90b4-10f7afdcc61b
-- title:
--   Eta Partial Sums: partial tendsto G
-- statement:
--   The Eta Partial Sums construction uses the partial tendsto G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensLsA.lean#L187-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensLsA.lean#L187-L199

import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_partial_tendsto_G

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.partial_tendsto_G {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, f n * (n : ℂ) ^ (-s)) atTop (𝓝 (G f s)) := by sorry
