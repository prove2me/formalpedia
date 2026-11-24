-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_RR_cN_le
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.RR_cN_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:01.428702+00:00
-- url     : https://prove2.me/theorems/104b4f54-7305-4f5d-96b8-91512c8e9020
-- title:
--   Logarithmic Integral Bounds: RR c N le
-- statement:
--   The Logarithmic Integral Bounds construction uses the RR c N le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L389-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L389-L476

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.RR_cN_le : ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (m₀ : ℕ) (y : ℝ), 1 ≤ y →
    (∀ p : ℕ, p.Prime → p ∣ m₀ → p ≤ ⌊x ^ 400⌋₊ → (p : ℝ) ≤ y) →
    RR (cN x) m₀ ⌊x ^ 400⌋₊ ≤ C * (Real.sqrt x + y * Real.log x) := by sorry
