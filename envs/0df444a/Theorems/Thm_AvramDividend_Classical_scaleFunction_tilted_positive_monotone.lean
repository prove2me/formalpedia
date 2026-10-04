-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
-- name    : AvramDividend.Classical.scaleFunction_tilted_positive_monotone
-- status  : Open
-- author  : @WillR
-- created : 2026-10-03T13:58:07.454679+00:00
-- url     : https://prove2.me/theorems/8d7288ac-aaf4-4acb-afec-ee519b6f78b8
-- title:
--   Strict positivity and Esscher normalised monotonicity of q scale function
-- statement:
--   Under the standing hypotheses and q>0, the q-scale function is positive on (0,∞), and there exists φ>0 such that x↦e^{-φx}W(x) is nondecreasing on (0,∞). A standard construction uses φ=Φ(q), an upward-first-passage transform or Wiener-Hopf potential-measure positivity. Requires a new stochastic argument, not supplied by the existing analytic children.
-- source:
--   Kuznetsov, Kyprianou and Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes (2012), Esscher identity and Wiener–Hopf factorisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The analytic positivity and Esscher-normalised monotonicity of a q-scale
function. This is the missing stochastic bridge, not an analytic tautology. -/
theorem scaleFunction_tilted_positive_monotone {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  sorry

end AvramDividend.Classical
