-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_alt_sum
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.alt_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:17:58.454073+00:00
-- url     : https://prove2.me/theorems/3ee5d193-25d5-4ae8-96df-c32bd09d656f
-- title:
--   Eta Partial Sums: alt sum
-- statement:
--   The Eta Partial Sums construction uses the alt sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensLs.lean#L102-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensLs.lean#L102-L125

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLs
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.alt_sum (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 (2 * N), (n : ℂ) ^ (-s) - (2 : ℂ) ^ (1 - s) * ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 (2 * N), eps n * (n : ℂ) ^ (-s) := by sorry
