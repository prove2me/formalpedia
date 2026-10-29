-- Prove2me | Theorems.Thm_EthierKurtz_oblique_halfspace_model_fails_lipschitz
-- name    : EthierKurtz.oblique_halfspace_model_fails_lipschitz
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-28T21:47:40.967983+00:00
-- url     : https://prove2.me/theorems/fb0ba85c-2255-4819-81f5-ea1403491eec
-- title:
--   The constant-coefficient half-space oblique model fails for $\mu=1$
-- statement:
--   Let $n\ge1$, $H=\{x\in\mathbb{R}^{n+1}: x_0>0\}$. There is no $\lambda_0>0$ such that for every bounded Lipschitz $h$ on $\overline H$ the problem $$\lambda_0 u-\tfrac12\Delta u=h \text{ in } H,\qquad -\partial_{x_0}u=0 \text{ on } \partial H$$ has a solution in the graph `obliqueDiffusionGraph` ($C^{2,1}$ regularity up to the boundary).
--
--   Role: disposes of the case $\mu=1$ of the parent, whose half-space model hypothesis is then false (the Schauder theory fails at the Lipschitz endpoint).
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7 (Lemma 6.29, Theorems 6.30-6.31: the theory requires $0<\mu<1$) and Problem 4.9 (failure of $C^{2,1}$ estimates); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
open Real MeasureTheory
open scoped BoundedContinuousFunction Topology
open Filter
open scoped Topology BoundedContinuousFunction
open EthierKurtz
open scoped BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_halfspace_model_fails_lipschitz (n : ℕ) (hd : 2 ≤ n + 1) : ¬ (∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ (h : (closure {x : EuclideanSpace ℝ (Fin (n + 1)) |
        (0 : ℝ) < x (0 : Fin (n + 1))}) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨1, zero_le_one⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph
          {x : EuclideanSpace ℝ (Fin (n + 1)) |
            (0 : ℝ) < x (0 : Fin (n + 1))} 1 (fun _ => 1) (fun _ => 0)
          (fun _ => EuclideanSpace.single (0 : Fin (n + 1)) (-1 : ℝ)),
          lam₀ • fg.1 - fg.2 = h) := by sorry

end EthierKurtz
