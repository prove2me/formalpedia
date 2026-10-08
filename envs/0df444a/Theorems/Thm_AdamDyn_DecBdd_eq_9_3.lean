-- Prove2me | Theorems.Thm_AdamDyn_DecBdd_eq_9_3
-- name    : AdamDyn.DecBdd.eq_9_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:25.55399+00:00
-- url     : https://prove2.me/theorems/011ad43b-ca01-4ede-9b82-ae8f02de4f73
-- title:
--   (9.3) — coordinatewise bound √v̂_n − √v̂_{n+1} ≤ c_{n+1}√v̂_{n+1}
-- statement:
--   Let $0\le\beta_n\le1$ for all $n$ and $\beta_1<1$, and let $(x_n,m_n,v_n)$ be the iterates of Algorithm 5.1 along any sample path (any $\gamma$, $\alpha$, $\varepsilon$, gradient values), with $\hat v_n=v_n/\bar r_n$. For every $n\ge1$ with $\beta_{n+1}>0$ and every coordinate $i$,
--   $$\sqrt{\hat v_{n,i}}-\sqrt{\hat v_{n+1,i}}\le c_{n+1}\sqrt{\hat v_{n+1,i}},\qquad c_{n+1}:=\frac{1-\beta_{n+1}}{\sqrt{\beta_{n+1}}}\Big(\frac1{1+\sqrt{\beta_{n+1}}}+\frac{1-\bar r_n}{2\bar r_n}\Big).$$
--
--   The bound controls how fast the adaptive denominator $\varepsilon+\sqrt{\hat v_n}$ can shrink in one step; since $c_n/\gamma_n\to b/2$, it yields the estimate on $D_{n+1}-D_n$ used to compare $P_{n+1}$ with $P_n$.
--
--   **Formalization Note** $\beta_{n+1}>0$ is required because $c_{n+1}$ divides by $\sqrt{\beta_{n+1}}$ (under Assumption 5.1 it holds for all large $n$); $n\ge1$ and $\beta_1<1$ make $\bar r_n>0$. The identity preceding (9.3) on the page is not stated, only the inequality.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, §9.2, p. 26, Eq. (9.3)

import Mathlib
import Definitions.Def_AdamDyn_DecBdd_Algorithm
import Definitions.Def_AdamDyn_DecBdd_ProofQuantities

namespace AdamDyn.DecBdd

/-- (9.3), §9.2, p. 26: coordinatewise, `√v̂_n - √v̂_{n+1} ≤ c_{n+1} √v̂_{n+1}` for every `n ≥ 1`
with `β_{n+1} > 0`, along every run of Algorithm 5.1. -/
theorem eq_9_3 {d : ℕ} {Ξ : Type*} (gf : AdamDyn.ConstStep.E d → Ξ → AdamDyn.ConstStep.E d)
    (γ α β : ℕ → ℝ) (ε : ℝ) (x0 : AdamDyn.ConstStep.E d)
    (hβ : ∀ n, 0 ≤ β n ∧ β n ≤ 1) (hβ1 : β 1 < 1)
    (ξs : ℕ → Ξ) (n : ℕ) (hn : 1 ≤ n) (hβpos : 0 < β (n + 1)) (i : Fin d) :
    Real.sqrt (vHat β n (adamRun gf γ α β ε x0 ξs n) i)
        - Real.sqrt (vHat β (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1)) i) ≤
      cCoef β n * Real.sqrt (vHat β (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1)) i) := by sorry

end AdamDyn.DecBdd
