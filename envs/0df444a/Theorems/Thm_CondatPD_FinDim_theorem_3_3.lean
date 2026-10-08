-- Prove2me | Theorems.Thm_CondatPD_FinDim_theorem_3_3
-- name    : CondatPD.FinDim.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:40:54.189813+00:00
-- url     : https://prove2.me/theorems/252b993a-882a-4b56-b210-948cbe7a637f
-- title:
--   Theorem 3.3, p. 6 — in finite dimension with F = 0 and στ‖L‖² ≤ 1, Algorithms 3.1 and 3.2 converge to a solution of (6)
-- statement:
--   Let $\mathcal X$ and $\mathcal Y$ be finite-dimensional real Hilbert spaces, $G\in\Gamma_0(\mathcal X)$, $H\in\Gamma_0(\mathcal Y)$ (proper, lower semicontinuous, convex, with values in $\mathbb R\cup\{+\infty\}$), $L:\mathcal X\to\mathcal Y$ linear, and suppose that the inclusion (6),
--   $$0\in\partial G(\hat x)+L^*\hat y+\nabla F(\hat x),\qquad 0\in-L\hat x+\partial H^*(\hat y),$$
--   has a solution. Let $\tau>0$, $\sigma>0$, let $(\rho_n)$, $(e_{F,n})$, $(e_{G,n})$, $(e_{H,n})$ be the parameters of Algorithms 3.1 and 3.2, and suppose that $F=0$, that every $e_{F,n}=0$, and that
--
--   1. $\sigma\tau\|L\|^2\le1$;
--   2. there is $\varepsilon>0$ with $\rho_n\in[\varepsilon,2-\varepsilon]$ for every $n\in\mathbb N$;
--   3. $\sum_{n\in\mathbb N}\|e_{G,n}\|<+\infty$ and $\sum_{n\in\mathbb N}\|e_{H,n}\|<+\infty$.
--
--   Then for every run $(x_n,y_n)$ of Algorithm 3.1, and for every run of Algorithm 3.2, there is a solution $(\hat x,\hat y)$ of (6) such that
--   $$x_n\to\hat x\qquad\text{and}\qquad y_n\to\hat y$$
--   in norm.
--
--   Compared with Theorem 3.2 (which needs $\sigma\tau\|L\|^2<1$ and gives only weak convergence), the equality case $\sigma\tau\|L\|^2=1$ is allowed, so one may set $\sigma=1/(\tau\|L\|^2)$ and tune only $\tau$, as in the Douglas–Rachford method.
--
--   **Formalization Note** The proximity operators are maps satisfying the minimisation property of $\mathrm{prox}_{\tau G}$ and $\mathrm{prox}_{\sigma H^*}$ ($H^*$ the Fenchel conjugate); for $G,H\in\Gamma_0$ they exist and are unique. The paper's standing assumption that (6) has a solution is a hypothesis; its other standing assumption (problem (1) has a minimiser) follows from it and is omitted. The limit pair is chosen after the run. Errors are not weighted by $\rho_n$, and $\varepsilon$ is fixed before $n$.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 6, Theorem 3.3; standing assumptions pp. 3–4, (1), (6)

import Mathlib
import Definitions.Def_CondatPD_FinDim_Setting

open InnerProductSpace Filter Topology

namespace CondatPD.FinDim

/-- Theorem 3.3, p. 6: in finite dimension, with `F = 0`, `e_{F,n} = 0`, (i) `στ‖L‖² ≤ 1`,
(ii) `ρₙ ∈ [ε, 2 − ε]` for some `ε > 0`, and (iii) summable errors, every run of Algorithm 3.1 and
every run of Algorithm 3.2 converges to a solution of (6). -/
theorem theorem_3_3 {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] [FiniteDimensional ℝ Y]
    (F : X → ℝ) (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (hF0 : F = 0)
    (hG : ThreeOpSplitting.ConvexRates.IsProperClosedConvex G)
    (hH : ThreeOpSplitting.ConvexRates.IsProperClosedConvex H)
    (hsol : ∃ (xh : X) (yh : Y), IsPDSolution F G H L xh yh)
    (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ)
    (PG : X → X) (PH : Y → Y)
    (hPG : ThreeOpSplitting.ConvexRates.IsProx τ G PG)
    (hPH : ThreeOpSplitting.ConvexRates.IsProx σ (conj H) PH)
    (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → Y)
    (heF : ∀ n, eF n = 0)
    (hi : σ * τ * ‖L‖ ^ 2 ≤ 1)
    (hii : ∃ ε : ℝ, 0 < ε ∧ ∀ n, ε ≤ ρ n ∧ ρ n ≤ 2 - ε)
    (hiii : Summable (fun n => ‖eG n‖) ∧ Summable (fun n => ‖eH n‖)) :
    (∀ (x : ℕ → X) (y : ℕ → Y), IsAlg31Run F PG PH τ σ L ρ eF eG eH x y →
      ∃ (xh : X) (yh : Y), IsPDSolution F G H L xh yh ∧
        Tendsto x atTop (𝓝 xh) ∧ Tendsto y atTop (𝓝 yh)) ∧
    (∀ (x : ℕ → X) (y : ℕ → Y), IsAlg32Run F PG PH τ σ L ρ eF eG eH x y →
      ∃ (xh : X) (yh : Y), IsPDSolution F G H L xh yh ∧
        Tendsto x atTop (𝓝 xh) ∧ Tendsto y atTop (𝓝 yh)) := by sorry

end CondatPD.FinDim
