-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_abel_core
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.abel_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:13.552669+00:00
-- url     : https://prove2.me/theorems/17f9ec6c-36c4-4c49-bab5-455973a7f0e3
-- title:
--   Primes In Progressions: abel core
-- statement:
--   The Primes In Progressions construction uses the abel core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L212-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L212-L328

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.abel_core (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hcΛ : ∀ n, c n ≤ ArithmeticFunction.vonMangoldt n)
    {K θ β D X : ℝ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1) (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (hX : 16 ≤ X)
    (hD : 0 ≤ D)
    (h : ∀ t, √X ≤ t → t ≤ X → |(∑ n ∈ Icc 0 ⌊t⌋₊, c n) - Fm K θ β t| ≤ D * t) :
    |∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * c n - K * (liX X - θ * liX (X ^ β))| ≤
      5 * D * X / Real.log X + 40 * √X := by sorry
