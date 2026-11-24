-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_avgLimit
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.avgLimit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:05.844317+00:00
-- url     : https://prove2.me/theorems/305021dd-1e44-4140-8cf8-1e27f7ed362f
-- title:
--   T2: avg Limit
-- statement:
--   The T2 construction uses the avg Limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/RootNorm.lean#L112-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/RootNorm.lean#L112-L144

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_RootNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.avgLimit {n : ℕ} (y : Fin n → ℂ) (hy : ∀ i, ‖y i‖ ≠ 1) (j : ℕ) (hj : 1 ≤ j) (K : ℝ)
    (hK : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖∑ i, (y i * ζ) ^ j / (1 - y i * ζ)‖ ≤ K) :
    ((univ.filter (fun i => 1 < ‖y i‖)).card : ℝ) ≤ K := by sorry
