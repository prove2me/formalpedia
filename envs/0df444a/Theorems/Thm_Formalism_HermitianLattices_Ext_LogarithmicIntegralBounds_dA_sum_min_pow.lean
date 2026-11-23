-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_sum_min_pow
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_sum_min_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:51.018402+00:00
-- url     : https://prove2.me/theorems/f6440dc9-1507-4a19-8f6a-1621ed963603
-- title:
--   Logarithmic Integral Bounds: d A sum min pow
-- statement:
--   The Logarithmic Integral Bounds construction uses the d A sum min pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L262-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L262-L300

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_sum_min_pow (x : ℝ) (hx : 1 ≤ x) (p : ℕ) (hp : 2 ≤ p) (L : ℕ) :
    Real.log p * ∑ i ∈ Icc 1 L, min 1 (x / (p : ℝ) ^ i) ≤ Real.log x + 2 * Real.log p := by sorry
