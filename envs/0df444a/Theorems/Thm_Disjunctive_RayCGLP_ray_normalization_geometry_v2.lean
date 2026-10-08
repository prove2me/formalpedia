-- Prove2me | Theorems.Thm_Disjunctive_RayCGLP_ray_normalization_geometry_v2
-- name    : Disjunctive.RayCGLP.ray_normalization_geometry_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:37.153724+00:00
-- url     : https://prove2.me/theorems/d9496a50-20cf-4e33-a432-18684d249fb9
-- title:
--   Corollary 10.4 — for $y=x^*-\bar x$, $(CGLP)_y$ has an optimal cut through a boundary point of $P_D$ on $(\bar x,x^*]$
-- statement:
--   Let $P_D\subseteq\mathbb R^n$ be the disjunctive hull, a polyhedron $\{x: Gx\ge g\}$, and let $\bar x\notin P_D$ be the point to be cut off. Let $y:=x^*-\bar x$ for some $x^*\in P_D$. Then the cut-generating LP under the ray normalization,
--   $$(CGLP)_y:\quad \min\{\alpha\bar x-\beta:\ \alpha x\ge\beta\ \ \forall x\in P_D,\ \ \alpha y=1\},$$
--   has an optimal solution $(\tilde\alpha,\tilde\beta)$ such that (i) $\tilde\alpha\bar x<\tilde\beta$, i.e. the cut $\tilde\alpha x\ge\tilde\beta$ cuts off $\bar x$, and (ii) $\tilde\alpha x=\tilde\beta$ is a supporting hyperplane of $P_D$: $\tilde\alpha x\ge\tilde\beta$ is valid for $P_D$, and the hyperplane meets the segment $(\bar x,x^*]$ at a point $\bar x+t(x^*-\bar x)$, $t\in(0,1]$, that belongs to $P_D$.
--
--   **Formalization Note.** The retired version omitted the standing hypothesis $\bar x\notin P_D$ ($\bar x$ is the LP optimum to be separated); with $\bar x=x^*$ the normalization $\alpha\cdot 0=1$ is infeasible. It also allowed $P_D$ to be any closed convex set, for which the minimum of $(CGLP)_y$ need not be attained (a disk tangent to the segment at $x^*$); in the book $P_D=\operatorname{cl}\operatorname{conv}\bigcup_i P_i$ for finitely many polyhedra, hence a polyhedron, which is now assumed. "Supporting" is made explicit by requiring the contact point to lie in $P_D$. The printed corollary's "$y:=\bar x$" is a misprint for $y:=x^*-\bar x$ (Fig. 10.3); the book's $P_Q$ is the same set as $P_D$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §10.6, p. 139, Corollary 10.4 — corrected transcription of the printed '$y:=\bar x$' to '$y:=x^*-\bar x$' (Fig. 10.3)

import Mathlib
import Definitions.Def_Disjunctive_RayCGLP_Basic

namespace Disjunctive.RayCGLP

/-- Corollary 10.4 (Balas, *Disjunctive Programming*, §10.6, p. 139, [32]): let `P_D` be the
disjunctive hull (a polyhedron) and `x̄ ∉ P_D` the point to be cut off. For `y := x* - x̄` with
`x* ∈ P_D`, `(CGLP)_y` has an optimal solution `(α̃, β̃)` such that (i) `α̃x̄ < β̃`, and
(ii) `α̃x = β̃` is a supporting hyperplane of `P_D` (`α̃x ≥ β̃` is valid for `P_D` and the
hyperplane touches `P_D`) meeting the segment `(x̄, x*]` at the point `x̄ + t(x* - x̄)`,
`t ∈ (0,1]`, which lies in `P_D`.

**Corrects a source typo**: the printed corollary reads "`y := x̄` for some `x* ∈ P_Q`"; the
figure caption (Fig. 10.3) gives `y = x* - x̄`. On the page `P_Q` is the same set as `P_D`.

Corrected from the retired version: (a) `x̄ ∉ P_D` is assumed, as throughout the section
(`x̄` is the LP optimum to be separated; for `x̄ ∈ P_D` no valid inequality cuts it off and for
`x̄ = x*` the normalization `α(x* - x̄) = 1` is infeasible); (b) `P_D` is a polyhedron
(`P_D = cl conv ∪ P_i` for finitely many polyhedra `P_i`), not just a closed convex set: for a
disk tangent to the segment the infimum of `(CGLP)_y` is not attained; (c) the contact point is
stated to lie in `P_D` ("supporting hyperplane"). -/
theorem ray_normalization_geometry_v2 {n m : ℕ} (G : Matrix (Fin m) (Fin n) ℝ) (g : Fin m → ℝ)
    (PD : Set (Fin n → ℝ)) (hPD : PD = {x | ∀ r, g r ≤ (G.mulVec x) r})
    (xbar xstar : Fin n → ℝ) (hxbar : xbar ∉ PD) (hxstar : xstar ∈ PD) :
    ∃ alphaT betaT, IsCGLPYOptimal PD (xstar - xbar) xbar alphaT betaT ∧
      dotProduct alphaT xbar < betaT ∧ (∀ x ∈ PD, betaT ≤ dotProduct alphaT x) ∧
      ∃ t : ℝ, IsGreatest
        {t' : ℝ | t' ∈ Set.Ioc (0 : ℝ) 1 ∧
          dotProduct alphaT (xbar + t' • (xstar - xbar)) = betaT} t ∧
        xbar + t • (xstar - xbar) ∈ PD := by sorry

end Disjunctive.RayCGLP
