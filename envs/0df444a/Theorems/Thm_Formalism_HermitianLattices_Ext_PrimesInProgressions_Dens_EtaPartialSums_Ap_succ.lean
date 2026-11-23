-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_Ap_succ
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.Ap_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:22.681039+00:00
-- url     : https://prove2.me/theorems/e78b468c-1e4f-41eb-9037-1793cb9d867e
-- title:
--   Eta Partial Sums: Ap succ
-- statement:
--   The Eta Partial Sums construction uses the Ap succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensLsA.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensLsA.lean#L23-L25

import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_Ap_succ

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.Ap_succ (n : ℕ) : Ap f (n + 1) = Ap f n + f (n + 1) := by sorry
