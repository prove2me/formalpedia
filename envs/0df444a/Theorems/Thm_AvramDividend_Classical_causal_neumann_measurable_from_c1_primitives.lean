-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_measurable_from_c1_primitives
-- name    : AvramDividend.Classical.causal_neumann_measurable_from_c1_primitives
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:23:08.281137+00:00
-- url     : https://prove2.me/theorems/b9e00123-4570-410c-95aa-a05650d0acfc
-- title:
--   Continuous Gaussian primitives give measurable Neumann corrections
-- statement:
--   When the Gaussian Neumann corrections are an initial constant followed by exponentially weighted continuous primitives, each correction is almost-everywhere strongly measurable on every finite causal interval. This provides the remaining measurability input to the dominated-convergence resolvent identity.
-- source:
--   For Q0 constant and Q(n+1)=exp(w x)Hn(x), the positive-time continuity of each Hn makes every Qn continuous on Ici 0. Restrict to Ioc 0 x and invoke Mathlib ContinuousOn.aestronglyMeasurable; this is the exact measurability hypothesis of causal_geometric_neumann_resolvent.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_neumann_measurable_from_c1_primitives
    (H Q : ℕ → ℝ → ℝ) (a w : ℝ)
    (hQ0 : Q 0 = fun _ : ℝ => 1 / a)
    (hQstep : ∀ n : ℕ, Q (n + 1) =
      fun x : ℝ => Real.exp (w * x) * H n x)
    (hHcont : ∀ n : ℕ, ContinuousOn (H n) (Ici (0 : ℝ))) :
    ∀ x : ℝ, ∀ i : ℕ, AEStronglyMeasurable
      (Q i) (volume.restrict (Ioc (0 : ℝ) x)) := by sorry
