-- Prove2me | Theorems.Thm_BERicci_Contract_eq_3_26
-- name    : BERicci.Contract.eq_3_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:58.820988+00:00
-- url     : https://prove2.me/theorems/82b38b95-d6d2-4b73-b42c-406ac0467c2d
-- title:
--   (3.26), p. 31 — W₂²(H_tδ_x, H_tδ_y) ≤ C²(t)d²(x,y)
-- statement:
--   Under the hypotheses of Theorem 3.5 ((MD), the length property (3.2), a strongly local Dirichlet form with mass-preserving heat flow, its dual semigroup $(\mathsf H_t)$, and the bounds (3.15), (3.16) with $C$ bounded on every $[0,T]$), for every $t\ge0$ and $x,y\in X$
--   $$W_2^2(\mathsf H_t\delta_x,\mathsf H_t\delta_y)\le C^2(t)\,\mathsf d^2(x,y).$$
--
--   This is the contraction estimate for Dirac masses; Theorem 3.5 extends it to arbitrary probability measures by gluing optimal plans between $\mathsf H_t\delta_x$ and $\mathsf H_t\delta_y$.
--
--   **Formalization Note** Both sides are in $[0,\infty]$; $W_2^2$ is the infimum over couplings of (3.12).
-- source:
--   arXiv:1209.5786v4, §3.2, proof of Theorem 3.5, (3.26), p. 31

import Mathlib
import Definitions.Def_BERicci_Contract_Bounds

namespace BERicci.Contract

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- (3.26), p. 31: `W₂²(H_t δ_x, H_t δ_y) ≤ C²(t) d²(x, y)` for all `t ≥ 0`, `x, y ∈ X`, under the
hypotheses of Theorem 3.5. -/
theorem eq_3_26
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (hsupp : m.IsOpenPosMeasure) (hMDb : BERicci.Gamma.MDb m)
    (E : (X → ℝ) → ℝ≥0∞) (hE : BERicci.Gamma.IsDirichletForm m E) (hloc : BERicci.Gamma.IsStronglyLocal m E)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : BERicci.Gamma.IsHeatSemigroup m E P) (hmass : MassPreserving m P)
    (hlen : BERicci.Gamma.IsLengthSpace X)
    (C : ℝ → ℝ≥0) (hC : BoundedOnIntervals C) (h315 : LipContraction m P C)
    (H : ℝ → Measure X → Measure X) (hH : IsDualSemigroup m P H) (h316 : GradBound m H C) :
    ∀ t : ℝ, 0 ≤ t → ∀ x y : X,
      BERicci.Gamma.W2sq (H t (Measure.dirac x)) (H t (Measure.dirac y)) ≤ ((C t : ℝ≥0∞)) ^ 2 * edist x y ^ 2 := by sorry

end BERicci.Contract
