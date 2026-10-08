-- Prove2me | Theorems.Thm_FastBestSubset_CDSS_lemma_1
-- name    : FastBestSubset.CDSS.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:20.90097+00:00
-- url     : https://prove2.me/theorems/ef04ebde-f234-49d6-82a5-b556f3855db7
-- title:
--   Lemma 1 — β is a stationary solution of Problem (2) iff ∇_S f(β) = 0 on its support S
-- statement:
--   Let $X$ have unit-norm columns, $\lambda_0>0$ and $\lambda_1,\lambda_2\ge0$. Let $\beta\in\mathbb R^p$ have support $S$. Then $\beta$ is a stationary solution of Problem (2) (Definition 1: $F'(\beta;d)\ge0$ for every direction $d$) if and only if
--   $$\nabla_S f(\beta)=0,$$
--   that is, for every $i\in S$ the function $t\mapsto f(\beta_1,\dots,\beta_{i-1},t,\beta_{i+1},\dots,\beta_p)$ is differentiable at $t=\beta_i$ with derivative $0$.
--
--   The lemma turns the directional-derivative definition of stationarity into a finite system of equations on the support, which is the form used in the convergence proof.
--
--   **Formalization Note** $f$ is differentiable in each coordinate $i$ with $\beta_i\neq0$ even when $\lambda_1>0$, so the partial gradient on $S$ is a genuine derivative; it is stated with `HasDerivAt`, which asserts existence as well as the value.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Lemma 1, p. 6 (proof §A.1, p. 36)

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

open Filter Topology

namespace FastBestSubset.CDSS

/-- Lemma 1 (p. 6): `β` (with support `S`) is a stationary solution of Problem (2) iff
`∇_S f(β) = 0`, i.e. for every `i ∈ Supp(β)` the partial derivative of `f` in coordinate `i`
exists at `β` and vanishes. -/
theorem lemma_1 {n p : ℕ} (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2) (β : Fin p → ℝ) :
    IsStationary D β ↔
      ∀ i ∈ supp β, HasDerivAt (fun t : ℝ => f D (Function.update β i t)) 0 (β i) := by sorry

end FastBestSubset.CDSS
