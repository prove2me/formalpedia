-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sum_log_sq_div_sq_primes_dyadic_le
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_log_sq_div_sq_primes_dyadic_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:12.942938+00:00
-- url     : https://prove2.me/theorems/cba25f08-6387-427e-9a45-92a5c774848b
-- title:
--   Logarithmic Integral Bounds: sum log sq div sq primes dyadic le
-- statement:
--   The Logarithmic Integral Bounds construction uses the sum log sq div sq primes dyadic le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagB.lean#L13-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagB.lean#L13-L70

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagB
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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_log_sq_div_sq_primes_dyadic_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 ≤
      2 * Real.log 4 * Real.log (2 * y) / y := by sorry
