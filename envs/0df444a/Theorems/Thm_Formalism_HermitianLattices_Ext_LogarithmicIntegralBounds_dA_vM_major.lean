-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_vM_major
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_vM_major
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:35.865008+00:00
-- url     : https://prove2.me/theorems/cac05a23-23f4-4446-a08a-59f4034f44b8
-- title:
--   Logarithmic Integral Bounds: d A v M major
-- statement:
--   The Logarithmic Integral Bounds construction uses the d A v M major property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L127-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L127-L149

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
open ArithmeticFunction (vonMangoldt)

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_vM_major (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg : ∀ n, 1 ≤ n → g (n + 1) ≤ g n) (N : ℕ) :
    ∑ n ∈ Icc 1 N, vonMangoldt n * g n ≤ dA_KC * ∑ n ∈ Icc 1 N, g n := by sorry
