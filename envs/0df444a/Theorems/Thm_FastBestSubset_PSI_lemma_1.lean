-- Prove2me | Theorems.Thm_FastBestSubset_PSI_lemma_1
-- name    : FastBestSubset.PSI.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:56.920992+00:00
-- url     : https://prove2.me/theorems/a560f576-03fc-4b04-826f-7291756105db
-- title:
--   Lemma 1 — β is stationary for Problem (2) iff the partial gradient of f on its support vanishes
-- statement:
--   Consider Problem (2) with unit-norm columns of $X$, $\lambda_0>0$ and $\lambda_1,\lambda_2\ge0$. Let $\beta^*\in\mathbb R^p$ have support $S$. Then $\beta^*$ is a stationary solution, meaning $F'(\beta^*;d)\ge0$ for every direction $d$, if and only if
--   $$\nabla_S f(\beta^*)=0,$$
--   i.e. for every $i\in S$ the partial derivative of $f$ with respect to $\beta_i$ exists at $\beta^*$ and equals $0$.
--
--   Since $\beta^*_i\neq0$ for $i\in S$, $f$ is differentiable in each coordinate of the support, so $\nabla_Sf(\beta^*)$ is a genuine partial gradient. The lemma turns the directional-derivative definition of stationarity into the explicit condition (5). The PSI($k$) minima of Theorem 4 are stationary by definition, so this is the bridge from the coordinate-wise conditions (8) to Definition 3.
--
--   **Formalization Note** "$\partial f/\partial\beta_i$ exists and equals $0$ at $\beta^*$" is stated with `HasDerivAt` for the map $t\mapsto f(\beta^*_1,\dots,t,\dots,\beta^*_p)$ at $t=\beta^*_i$. `deriv` is not used, because it would return $0$ at points of non-differentiability. Stationarity uses the `EReal`-valued lower directional derivative.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Lemma 1, p. 6

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

namespace FastBestSubset.PSI

/-- Lemma 1 (p. 6): `β` (with support `S`) is a stationary solution of Problem (2) iff
`∇_S FastBestSubset.CDSS.f(β) = 0`, i.e. for every `i ∈ Supp(β)` the partial derivative of `f` in coordinate `i`
exists at `β` and vanishes. -/
theorem lemma_1 {n p : ℕ} (D : FastBestSubset.CDSS.Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2) (β : Fin p → ℝ) :
    FastBestSubset.CDSS.IsStationary D β ↔
      ∀ i ∈ FastBestSubset.CDSS.supp β, HasDerivAt (fun t : ℝ => FastBestSubset.CDSS.f D (Function.update β i t)) 0 (β i) := by sorry

end FastBestSubset.PSI
