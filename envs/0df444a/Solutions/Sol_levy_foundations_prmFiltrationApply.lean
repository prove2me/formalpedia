-- Prove2me | solution 1 for levy_foundations_prmFiltrationApply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:50:50.018168+00:00
-- url     : https://prove2.me/submissions/79ea572f-1cf5-4d44-93f7-4ac75408b4f2

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_levy_foundations_prmFiltration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × E)
    (m : Measure E) [SigmaFinite m]
    (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n))
    (t : ℝ≥0) :
    LevyFoundations.prmFiltration K X m hK hX t =
      LevyFoundations.prmEvalSigma K X (volume.prod m)
        (Set.Iic (t : ℝ) ×ˢ Set.univ) := by
  rfl
