-- Prove2me | Theorems.Thm_AndersonAccel_Safe_aais_converges
-- name    : AndersonAccel.Safe.aais_converges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:13:09.711985+00:00
-- url     : https://prove2.me/theorems/374fa668-e447-4867-b122-aa342a39e2b6
-- title:
--   Theorem 4.1 — stabilized type-I Anderson acceleration converges to a fixed point of every nonexpansive map
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^n$ be nonexpansive in the Euclidean norm, $\|f(x)-f(y)\|_2\le\|x-y\|_2$ for all $x,y$, and suppose its fixed-point set $X=\{x^\star\mid x^\star=f(x^\star)\}$ is nonempty. Run Algorithm 3.1 (AA-I-S-m) from any $x^0$ with regularization constants $\bar\theta,\tau,\alpha\in(0,1)$, safeguarding constants $D,\epsilon>0$ and max-memory $m\ge1$. Then there is a fixed point $x^\star=f(x^\star)$ with
--   $$\lim_{k\to\infty}x^k=x^\star.$$
--
--   This is the global convergence guarantee for the stabilized type-I Anderson acceleration: no smoothness, contractivity or local assumption on $f$ is needed, only nonexpansiveness and existence of a solution, the same hypotheses under which the unaccelerated averaged iteration converges.
--
--   **Formalization Note** The algorithm is the predicate `IsAAISRun` (line 9 as in Eq. (3.3) at a window start; see that definition). There is no hypothesis that the iterates avoid the solution set: if some $x^k$ is a fixed point, all later iterates equal it. $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Zhang, O'Donoghue, Boyd, SIAM J. Optim. 30 (2020), p. 3182, Theorem 4.1 (standing assumptions p. 3170)

import Mathlib
import Definitions.Def_AndersonAccel_Safe_Basic
import Definitions.Def_AndersonAccel_Safe_IsAAISRun

namespace AndersonAccel.Safe

open Filter Topology

/-- Theorem 4.1 (p. 3182). For a nonexpansive `f : ℝⁿ → ℝⁿ` with a fixed point, the iterates
`x^k` of Algorithm 3.1 converge to a fixed point `x⋆ = f(x⋆)`. -/
theorem aais_converges {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : LipschitzWith 1 f)
    (θbar τ α D ε : ℝ) (m : ℕ)
    (hθ0 : 0 < θbar) (hθ1 : θbar < 1) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hα0 : 0 < α) (hα1 : α < 1)
    (hD : 0 < D) (hε : 0 < ε) (hm : 0 < m)
    (x xt s y shat ytil : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) (mem nAA : ℕ → ℕ)
    (hrun : IsAAISRun f θbar τ α D ε m x xt s y shat ytil H mem nAA)
    (hX : ∃ z, f z = z) :
    ∃ xs : EuclideanSpace ℝ (Fin n), f xs = xs ∧ Tendsto x atTop (𝓝 xs) := by sorry

end AndersonAccel.Safe
