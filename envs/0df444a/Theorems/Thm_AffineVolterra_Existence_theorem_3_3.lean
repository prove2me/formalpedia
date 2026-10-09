-- Prove2me | Theorems.Thm_AffineVolterra_Existence_theorem_3_3
-- name    : AffineVolterra.Existence.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:04:21.019995+00:00
-- url     : https://prove2.me/theorems/3a92eb83-b46a-4c47-9dd0-42289fda58a0
-- title:
--   Theorem 3.3 — unique continuous strong solution for Lipschitz coefficients
-- statement:
--   Suppose $b:\mathbb R^d\to\mathbb R^d$ and $\sigma:\mathbb R^d\to\mathbb R^{d\times m}$ are Lipschitz, and every entry of the kernel $K$ satisfies condition (2.5), with an exponent that may depend on the entry. On every usual stochastic basis carrying an adapted $m$-dimensional Brownian motion $W$, and for every deterministic $x_0\in\mathbb R^d$, there is a continuous strong solution of (1.1). Every other continuous solution on that basis driven by the same $W$ and starting at $x_0$ is indistinguishable from it:
--
--   $$
--   \mathbb P\{\forall t\ge0,\ Y_t=X_t\}=1.
--   $$
--
--   This gives the strong existence and pathwise uniqueness step used to construct approximating solutions.
--
--   **Formalization Note** Strong adaptation is to the completed natural filtration of $W$; the deterministic initial condition contributes only a trivial initial sigma-algebra.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, Theorem 3.3, p. 13; proof, pp. 37–38

import Mathlib
import Definitions.Def_AffineVolterra_Existence_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AffineVolterra.Existence

/-- Theorem 3.3, p. 13: strong existence and pathwise uniqueness. -/
theorem theorem_3_3 {d m : ℕ} (K : Kernel d)
    (b : State d → State d) (σ : Diffusion d m)
    (hK : ∀ i j, ∃ γ : ℝ, Cond25 (fun t => K t i j) γ)
    (hlip : LipschitzCoefficients b σ) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
      (W : ℝ≥0 → Ω → State m) (x₀ : State d),
      IsUsualBasis P ℱ → IsFBrownian P ℱ W →
      ∃ X : ℝ≥0 → Ω → State d,
        IsStrongSolution P ℱ K b σ x₀ W X ∧
        ∀ Y : ℝ≥0 → Ω → State d,
          IsSolution P ℱ K b σ x₀ W Y →
          ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Y t ω = X t ω := by sorry

end AffineVolterra.Existence
