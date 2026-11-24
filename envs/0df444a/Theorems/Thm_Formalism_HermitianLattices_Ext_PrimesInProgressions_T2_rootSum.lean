-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_rootSum
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.rootSum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:30.984961+00:00
-- url     : https://prove2.me/theorems/324ff623-97d9-4119-a992-0ea67055122c
-- title:
--   T2: root Sum
-- statement:
--   The T2 construction uses the root Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/RootNorm.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/RootNorm.lean#L9-L20

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.rootSum (N : ℕ) (hN : 0 < N) (t : ℕ) (ht : t < N) :
    ∑ k ∈ range N, (cexp (2 * Real.pi * I / N) ^ k) ^ t = if t = 0 then (N : ℂ) else 0 := by sorry
