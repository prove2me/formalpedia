-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_sum_split
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_sum_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:24.251833+00:00
-- url     : https://prove2.me/theorems/5ef964f6-cd26-4f70-b130-13de2852bda4
-- title:
--   Logarithmic Integral Bounds: d A sum split
-- statement:
--   The Logarithmic Integral Bounds construction uses the d A sum split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L171-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L171-L183

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_sum_split (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n ≤ 1) (T : ℕ) (B : ℝ)
    (hB : ∀ M, T ≤ M → ∑ n ∈ Ioc T M, u n ≤ B) (M : ℕ) : ∑ n ∈ Icc 1 M, u n ≤ T + B := by sorry
