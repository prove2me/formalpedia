-- Prove2me | Theorems.Thm_DiffVI_Exist_prop_6_4
-- name    : DiffVI.Exist.prop_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:22.771404+00:00
-- url     : https://prove2.me/theorems/c4995e99-ecab-4566-8792-859125f9fe74
-- title:
--   Proposition 6.4, p. 34 — for psd D and 0 ∈ K: SOL(K, r, D) nonempty convex on int 𝒦(K, D)*; (a) R₀ pairs give (6.8); (b) polyhedral K gives (6.8) and L_D
-- statement:
--   Let $K\subseteq\mathbb R^m$ be a nonempty closed convex set containing the origin, and let $D$ be an $m\times m$ positive semidefinite matrix. Write $\mathrm{SOL}(K,r,D)=\mathrm{SOL}(K,r+D\,\cdot)$, let $\mathcal K(K,D)$ be the VI kernel (6.7), $\mathcal K(K,D)^*$ its dual cone and $\operatorname{int}\mathcal K(K,D)^*$ the interior of the latter in $\mathbb R^m$.
--   1. For every $r\in\operatorname{int}\mathcal K(K,D)^*$, $\mathrm{SOL}(K,r,D)$ is a nonempty convex set on which $(D+D^T)u$ is constant.
--   2. (a) If $(K,D)$ is an R₀ pair, there is $\rho>0$ such that for all $r\in\mathbb R^m$, $\mathrm{SOL}(K,r,D)\neq\emptyset$ and
--   $$\sup\{\|u\|:u\in\mathrm{SOL}(K,r,D)\}\le\rho(1+\|r\|).\qquad(6.8)$$
--   3. (b) If $K$ is a polyhedron, then (6.8) holds (for some $\rho>0$) for all $r\in\operatorname{int}\mathcal K(K,D)^*$, and there is $L_D>0$ with
--   $$\|(D+D^T)(u-u')\|\le L_D\|r-r'\|$$
--   for all $r,r'\in\mathcal K(K,D)^*$, $u\in\mathrm{SOL}(K,r,D)$, $u'\in\mathrm{SOL}(K,r',D)$.
--
--   This supplies the linear growth and convexity for the affine cases (c) and (d) of Theorem 6.1.
--
--   **Formalization Note** The page states the Lipschitz property "on $\mathcal K(K,D)$" and "for $r$ and $r'$ in $\mathcal K(K,D)$"; its proof establishes solvability and the constant $L_D$ on the dual cone $\mathcal K(K,D)^*$, which is the domain used here. Positive semidefiniteness does not assume symmetry.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 34, Proposition 6.4 (a), (b), (6.7), (6.8); proof pp. 34–37

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Exist_Setting

open MeasureTheory
open scoped InnerProductSpace InnerProduct

namespace DiffVI.Exist

/-- Proposition 6.4, p. 34: `K` closed convex containing `0`, `D` positive semidefinite. For every
`r ∈ int 𝒦(K, D)*`, `SOL(K, r, D)` is nonempty and convex and `(D + Dᵀ)u` is constant on it.
(a) If `(K, D)` is an R₀ pair, `SOL(K, r, D) ≠ ∅` and (6.8) hold for all `r`.
(b) If `K` is a polyhedron, (6.8) holds on `int 𝒦(K, D)*` and `r ↦ (D + Dᵀ)SOL(K, r, D)` is
Lipschitz on `𝒦(K, D)*` (the page prints `𝒦(K, D)`; its proof establishes it on the dual cone). -/
theorem prop_6_4 {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hKne : K.Nonempty)
    (hKcl : IsClosed K) (hKcv : Convex ℝ K) (hK0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ K)
    (D : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hD : IsPSD D) :
    (∀ r ∈ interior (dualCone (viKernel K D)),
      (SolodovSvaiterVI.Alg21.viSol (fun v => r + D v) K).Nonempty ∧
      Convex ℝ (SolodovSvaiterVI.Alg21.viSol (fun v => r + D v) K) ∧
      ∀ u ∈ SolodovSvaiterVI.Alg21.viSol (fun v => r + D v) K,
        ∀ u' ∈ SolodovSvaiterVI.Alg21.viSol (fun v => r + D v) K,
          (D + D†) u = (D + D†) u') ∧
    (IsR0Pair K D → ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : EuclideanSpace ℝ (Fin m),
      (SolodovSvaiterVI.Alg21.viSol (fun v => r + D v) K).Nonempty ∧
      ∀ u ∈ SolodovSvaiterVI.Alg21.viSol (fun v => r + D v) K, ‖u‖ ≤ ρ * (1 + ‖r‖)) ∧
    (IsPolyhedron K →
      (∃ ρ : ℝ, 0 < ρ ∧ ∀ r ∈ interior (dualCone (viKernel K D)),
        ∀ u ∈ SolodovSvaiterVI.Alg21.viSol (fun v => r + D v) K, ‖u‖ ≤ ρ * (1 + ‖r‖)) ∧
      ∃ LD : ℝ, 0 < LD ∧ ∀ r ∈ dualCone (viKernel K D), ∀ r' ∈ dualCone (viKernel K D),
        ∀ u ∈ SolodovSvaiterVI.Alg21.viSol (fun v => r + D v) K,
        ∀ u' ∈ SolodovSvaiterVI.Alg21.viSol (fun v => r' + D v) K,
          ‖(D + D†) (u - u')‖ ≤ LD * ‖r - r'‖) := by sorry

end DiffVI.Exist
