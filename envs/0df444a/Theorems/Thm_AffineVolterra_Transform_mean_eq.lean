-- Prove2me | Theorems.Thm_AffineVolterra_Transform_mean_eq
-- name    : AffineVolterra.Transform.mean_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:55.238403+00:00
-- url     : https://prove2.me/theorems/b5aaa2ae-0bf2-4f5f-a924-520bec33ea9d
-- title:
--   Proof of Theorem 4.3 — mean Volterra equation
-- statement:
--   If $X$ is an affine Volterra process with deterministic initial state $x_0$, its mean $m(t)=\mathbb E[X_t]$ is finite for every $t$ and satisfies
--
--   $$
--   m(t)-x_0=\bigl(K*(b^0+Bm)\bigr)(t),\qquad t\ge0.
--   $$
--
--   This identity relates the stochastic equation to a deterministic linear Volterra equation and is used to identify the initial value in Theorem 4.3.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, proof of Theorem 4.3, p. 20, paragraph after (4.10)

import Mathlib
import Definitions.Def_AffineVolterra_Transform_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace AffineVolterra.Transform

/-- The mean equation used in the proof of Theorem 4.3, p. 20. -/
theorem mean_eq {Ω : Type} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (K : RKernel d) (D : AffineData d)
    (σ : State d → Matrix (Fin d) (Fin d) ℝ) (E : Set (State d))
    (x₀ : State d) (W X : ℝ≥0 → Ω → State d)
    (hX : IsAffineVolterra P ℱ K D σ E x₀ W X) :
    (∀ t, Integrable (X t) P) ∧
    ∀ t : ℝ≥0, ∀ i,
      (∫ ω, X t ω i ∂P) - x₀ i =
        ∑ j, ∫ s in (0 : ℝ)..t.val,
          K (t.val - s) i j *
            (D.bv 0 j + ∑ k, Bmat D j k * (∫ ω, X s.toNNReal ω k ∂P)) := by sorry

end AffineVolterra.Transform
