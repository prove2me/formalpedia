-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_final_ineq
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.final_ineq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:36.332877+00:00
-- url     : https://prove2.me/theorems/0330ee06-4882-4980-b830-c3b82aaa42c6
-- title:
--   Logarithmic Integral Bounds: final ineq
-- statement:
--   The Logarithmic Integral Bounds construction uses the final ineq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistC.lean#L82-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistC.lean#L82-L214

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
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
set_option maxHeartbeats 1000000

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.final_ineq (ε c₀ c₃ A₀ C₀ L u lm ℓm ℓ : ℝ) (hε : 0 < ε) (hc₀ : 0 < c₀) (hc₃ : 0 < c₃)
    (hL1 : 2 ≤ L) (hL2 : 8 * (ε / 5 + 5 + Real.log 128) / c₀ ≤ L)
    (hL3 : 8 * (3 + Real.log (32 * (|A₀| + 1))) / c₃ ≤ L) (hL4 : Real.log (32 * (|A₀| + 1)) ≤ L)
    (hL5 : 8 * |C₀| * (Real.log 806 + ε / 5 + 1) ≤ L)
    (hu1 : (1 / 4) * L ^ 2 * ℓm ≤ u) (hu2 : (200 + 16 / c₃) * L ^ 3 ≤ u)
    (hlogu : Real.log u ≤ (ε / 5 + 2) * L)
    (hℓm : ℓm ≤ 4 * Real.exp (ε / 5 * L))
    (hlm0 : 2 ≤ lm) (hlm : lm ≤ ℓ) (hℓ : ℓ ≤ ℓm + 800 * L) :
    C₀ * lm * Real.log (lm + 2) ≤ u ∧
    16 * u * Real.exp (-(c₀ / ℓ * u)) ≤ Real.exp (-(3 * L)) / 8 ∧
    2 * |A₀| * (Real.exp (-(c₃ * u / lm)) + Real.exp (-Real.sqrt (c₃ * u))) ≤ Real.exp (-(3 * L)) / 8 ∧
    Real.exp (-(2 / 5 * u)) ≤ Real.exp (-(3 * L)) / 4 := by sorry
