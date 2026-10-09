-- Prove2me | Theorems.Thm_AffineVolterra_Existence_theorem_3_4
-- name    : AffineVolterra.Existence.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:04:00.797315+00:00
-- url     : https://prove2.me/theorems/e914e079-8201-410e-83b5-2c102ec25d5a
-- title:
--   Theorem 3.4 — continuous weak existence with a first-kind resolvent
-- statement:
--   Let $K$ be a matrix-valued kernel with a resolvent of the first kind, and suppose every entry of $K$ satisfies condition (2.5). If $b$ and $\sigma$ are continuous and obey the linear-growth condition (3.1), then for every deterministic $x_0\in\mathbb R^d$ the stochastic Volterra equation (1.1) admits a continuous weak solution:
--
--   $$
--   \forall x_0\in\mathbb R^d,\quad \exists\ (\Omega,\mathcal F,(\mathcal F_t),\mathbb P,W,X)\ \text{solving (1.1)}.
--   $$
--
--   This is the general weak-existence result applied to the shifted approximating coefficients in the proof of Theorem 3.6.
--
--   **Formalization Note** The stochastic basis is existential, as required by weak existence. A matrix-valued resolvent is represented by locally finite signed entries through their positive and negative measure parts.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, Theorem 3.4, p. 13; proof, p. 39

import Mathlib
import Definitions.Def_AffineVolterra_Existence_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AffineVolterra.Existence

/-- Theorem 3.4, p. 13: weak existence under a first-kind resolvent. -/
theorem theorem_3_4 {d m : ℕ} (K : Kernel d)
    (b : State d → State d) (σ : Diffusion d m)
    (hres : HasResolventFirstKind K)
    (hK : ∀ i j, ∃ γ : ℝ, Cond25 (fun t => K t i j) γ)
    (hb : Continuous b) (hσ : Continuous σ)
    (cLG : ℝ) (hgrowth : LinGrowth b σ cLG) :
    ∀ x₀ : State d, HasWeakSolution K b σ x₀ Set.univ := by sorry

end AffineVolterra.Existence
