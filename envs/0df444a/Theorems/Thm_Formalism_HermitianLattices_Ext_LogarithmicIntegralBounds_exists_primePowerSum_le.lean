-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_exists_primePowerSum_le
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.exists_primePowerSum_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:25.861796+00:00
-- url     : https://prove2.me/theorems/62ef3da6-7ac2-4afd-8009-29fde73481fd
-- title:
--   Logarithmic Integral Bounds: exists prime Power Sum le
-- statement:
--   The Logarithmic Integral Bounds construction uses the exists prime Power Sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L357-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L357-L357

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.exists_primePowerSum_le : ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ p : ℕ, sP (cN x) ⌊x ^ 400⌋₊ p ≤ C * Real.log x := by sorry
