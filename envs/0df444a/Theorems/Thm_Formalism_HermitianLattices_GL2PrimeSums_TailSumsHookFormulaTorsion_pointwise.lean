-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_pointwise
-- name    : Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.pointwise
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:44.834223+00:00
-- url     : https://prove2.me/theorems/00bf10f4-7874-45b4-aeb5-4c8bdf55e1ba
-- title:
--   Tail Sums Hook Formula Torsion: pointwise
-- statement:
--   The Tail Sums Hook Formula Torsion construction uses the pointwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L298-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L298-L380

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion

theorem Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.pointwise (a : ℕ → ℂ) (Q C₁ c₁ : ℝ) (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hQ : 0 < Q)
    (hL : 1 ≤ Real.log Q)
    (H1 : ∀ u : ℝ, 2 ≤ u → ‖psum a u‖ ≤
          C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2))
    (H2 : ∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u →
          ‖psum a u‖ ≤ C₁ * u * Real.exp (-c₁ * Real.sqrt (Real.log u)))
    (n : ℕ) (hn : 3 ≤ n) :
    ‖∑ k ∈ Icc 1 n, a k‖ ≤
      n * (C₁ * ((n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2) +
        (C₁ * (4 * Real.log Q ^ 8 * Real.exp (-Real.log Q) +
          384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * Real.log Q)))) * (1 / Real.log (n : ℝ) ^ 2)) := by sorry
