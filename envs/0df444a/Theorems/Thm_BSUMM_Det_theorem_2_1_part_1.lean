-- Prove2me | Theorems.Thm_BSUMM_Det_theorem_2_1_part_1
-- name    : BSUMM.Det.theorem_2_1_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:00.166701+00:00
-- url     : https://prove2.me/theorems/c57f30ae-021b-4485-a9ae-f019146dd709
-- title:
--   Theorem 2.1(1) — BSUM-M: ‖Ex^r − q‖ → 0, ‖x^r − x^{r+1}‖ → 0, ‖x^r − x̄^r‖ → 0, and limit points are primal-dual optimal
-- statement:
--   Consider problem (1.1) under Assumption A, with approximation functions $u_k$ satisfying Assumption B, and suppose the error bound of Lemma 2.2 holds globally on $X$: there is $\tau>0$ with
--   $$\operatorname{dist}(x,X(y))\le\tau\,\|\tilde\nabla_xL(x;y)\|\qquad\text{for all }x\in X\text{ and all }y,$$
--   where $\tilde\nabla_xL$ is the proximal gradient (2.3) for $h$ plus the indicator of $X$. Then there is a threshold $\bar\alpha>0$ such that the following holds for every stepsize sequence $\alpha^r>0$ obeying one of the two rules
--
--   1. (constant) $\alpha^r=\alpha$ for all $r\ge1$, with $\alpha\le\bar\alpha$;
--   2. (diminishing) $\sum_{r=1}^\infty\alpha^r=\infty$ and $\lim_{r\to\infty}\alpha^r=0$, (2.22)
--
--   and for every run $\{(x^r,y^r)\}$ of BSUM-M (1.12):
--   $$\lim_{r\to\infty}\|Ex^r-q\|=0,\qquad\lim_{r\to\infty}\|x^r-x^{r+1}\|=0,\qquad\lim_{r\to\infty}\|x^r-\bar x^r\|=0,$$
--   where $\bar x^r$ is the point of $X(y^r)$ nearest to $x^r$; and every limit point $(x^\infty,y^\infty)$ of $\{(x^r,y^r)\}$ is a primal and dual optimal solution: $x^\infty$ solves (1.1) and $y^\infty$ maximizes the augmented dual $d$.
--
--   This is the convergence theorem for the cyclic block successive upper-bound minimization method of multipliers: a Gauss–Seidel sweep of inexact (majorized) block minimizations followed by a dual gradient step solves multi-block linearly constrained convex problems without strong convexity of the objective.
--
--   **Formalization Note** "Sufficiently small" is the existential threshold $\bar\alpha$, chosen after the problem data, the $u_k$ and the error bound and before the stepsizes and the run. Rule (2.22) is written $\neg\,\mathrm{Summable}\ \alpha$ (with positive terms, equivalent to divergence of the sum; finitely many terms, such as the unused index 0, do not matter) together with $\alpha^r\to0$. $\|x^r-\bar x^r\|$ is $\operatorname{dist}(x^r,X(y^r))$. Limit points are cluster points of the joint sequence in $\mathbb R^n\times\mathbb R^m$; nothing is claimed about boundedness or convergence of $\{y^r\}$. The error bound is assumed, as in the theorem, not derived: the page's Lemma 2.2 does not hold under Assumption A alone ($\ell(t)=t^4$, $K=1$, $E=0$, $X=[-1,1]$ gives a proximal gradient of order $|x|^3$ against $\operatorname{dist}(x,X(y))=|x|$). The prox includes $X$ and $d$ is a minimum over $X$ (see the setting).
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 15, Theorem 2.1 (1), (2.22)

import Mathlib
import Definitions.Def_BSUMM_Det_Setting

namespace BSUMM.Det

open Filter Topology

/-- Theorem 2.1, part 1 (Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 15).
Under Assumption A (standing), Assumption B and the error bound of Lemma 2.2 (global form on `X`,
for the proximal gradient of `h + ι_X`), there is a threshold `ᾱ > 0` such that for every
stepsize sequence `α^r > 0` that is either constant `α^r = α ≤ ᾱ` (rule i) or satisfies
`∑ α^r = ∞`, `α^r → 0` (rule ii, (2.22)), every BSUM-M run satisfies
`‖Ex^r − q‖ → 0`, `‖x^r − x^{r+1}‖ → 0`, `dist(x^r, X(y^r)) = ‖x^r − x̄^r‖ → 0`, and every limit
point `(x^∞, y^∞)` of `{(x^r, y^r)}` is a primal and dual optimal solution. -/
theorem theorem_2_1_part_1 {K : ℕ} {n : Fin K → ℕ} {m p : ℕ} (D : Data K n m p)
    (hA : D.AssumptionA) (u : (k : Fin K) → EuclideanSpace ℝ (Fin (n k)) → Xsp K n → ℝ)
    (hB : D.AssumptionB u) (hEB : D.ErrorBound) :
    ∃ αbar : ℝ, 0 < αbar ∧ ∀ α : ℕ → ℝ, (∀ r, 0 < α r) →
      ((∃ a : ℝ, a ≤ αbar ∧ ∀ r, 1 ≤ r → α r = a) ∨ (¬ Summable α ∧ Tendsto α atTop (𝓝 0))) →
      ∀ (x : ℕ → Xsp K n) (y : ℕ → EuclideanSpace ℝ (Fin m)), D.IsRun u α x y →
        Tendsto (fun r => ‖D.Emul (x r) - D.q‖) atTop (𝓝 0) ∧
        Tendsto (fun r => ‖x r - x (r + 1)‖) atTop (𝓝 0) ∧
        Tendsto (fun r => Metric.infDist (x r) (D.Xopt (y r))) atTop (𝓝 0) ∧
        ∀ (xs : Xsp K n) (ys : EuclideanSpace ℝ (Fin m)),
          MapClusterPt (xs, ys) atTop (fun r => (x r, y r)) → D.IsPrimalOpt xs ∧ D.IsDualOpt ys := by sorry

end BSUMM.Det
