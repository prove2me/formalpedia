-- Prove2me | Theorems.Thm_CondatPD_PPA_theorem_3_2
-- name    : CondatPD.PPA.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:35:52.863258+00:00
-- url     : https://prove2.me/theorems/e8013db9-0803-47b9-87db-697a5ecee4cb
-- title:
--   Theorem 3.2, p. 5 — with F = 0 and στ‖L‖² < 1, Algorithms 3.1 and 3.2 converge weakly to a solution of (6)
-- statement:
--   Let $\mathcal X,\mathcal Y$ be real Hilbert spaces, $L:\mathcal X\to\mathcal Y$ a bounded linear operator, $G\in\Gamma_0(\mathcal X)$, $H\in\Gamma_0(\mathcal Y)$, and suppose the primal–dual inclusion (6),
--   $$0\in\partial G(\hat x)+L^*\hat y+\nabla F(\hat x),\qquad 0\in-L\hat x+\partial H^*(\hat y),$$
--   has a solution. Let $\tau>0$, $\sigma>0$, let $(\rho_n)$, $(e_{F,n})$, $(e_{G,n})$, $(e_{H,n})$ be the parameters of Algorithms 3.1 and 3.2, and suppose that $F=0$, that the error terms $e_{F,n}$ are all zero, and that
--
--   1. $\sigma\tau\|L\|^2<1$,
--   2. $\rho_n\in\,]0,2[$ for every $n\in\mathbb N$,
--   3. $\displaystyle\sum_{n\in\mathbb N}\rho_n(2-\rho_n)=+\infty$,
--   4. $\displaystyle\sum_{n\in\mathbb N}\rho_n\|e_{G,n}\|<+\infty$ and $\displaystyle\sum_{n\in\mathbb N}\rho_n\|e_{H,n}\|<+\infty$.
--
--   Then, for every run $(x_n,y_n)$ of Algorithm 3.1, and for every run of Algorithm 3.2, from any initial point, there is a solution $(\hat x,\hat y)$ of (6) such that
--   $$x_n\rightharpoonup\hat x\qquad\text{and}\qquad y_n\rightharpoonup\hat y\qquad(n\to\infty),$$
--   weakly in $\mathcal X$ and $\mathcal Y$. In particular $\hat x$ minimizes $G+H\circ L$ and $\hat y$ solves the dual problem.
--
--   Unlike Theorem 3.1, the condition $\sigma\tau\|L\|^2<1$ involves no Lipschitz constant and the relaxation may approach $2$: this is the regime in which the method is the proximal point algorithm in a modified metric, and it contains the Chambolle–Pock algorithm.
--
--   **Formalization Note** $\Gamma_0$ is the published `IsProperClosedConvex` for `EReal`-valued functions, and $\mathrm{prox}_{\tau G}$, $\mathrm{prox}_{\sigma H^*}$ are maps $P_G,P_H$ with the published `IsProx` property (they exist and are unique for $\Gamma_0$ functions and positive parameters). $F$ stays a parameter of the algorithms with the hypothesis $F=0$, so the standing smoothness assumption (2) on $F$ holds trivially and is not stated; the standing assumption "the set of minimizers of (1) is nonempty" (p. 3) is implied by the nonemptiness of the solution set of (6) and is omitted. The series conditions are partial sums tending to $+\infty$ and summability of nonnegative series. The solution $(\hat x,\hat y)$ is chosen after the run, as the run's starting point is arbitrary. Weak convergence is $\langle x_n,v\rangle\to\langle\hat x,v\rangle$ for all $v$.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 5, Theorem 3.2; standing assumptions p. 3 (problem (1)) and p. 4 (solutions of (6) nonempty)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_CondatPD_PPA_Setting

open Filter Topology

namespace CondatPD.PPA

theorem theorem_3_2 {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → ℝ) (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (hF0 : F = 0)
    (hG : ThreeOpSplitting.ConvexRates.IsProperClosedConvex G)
    (hH : ThreeOpSplitting.ConvexRates.IsProperClosedConvex H)
    (hsol : ∃ (xh : X) (yh : Y), IsPDSolution F G H L xh yh)
    (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (PG : X → X) (PH : Y → Y)
    (hPG : ThreeOpSplitting.ConvexRates.IsProx τ G PG)
    (hPH : ThreeOpSplitting.ConvexRates.IsProx σ (MoreauProx.Characterization.conj H) PH)
    (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → Y)
    (heF : ∀ n, eF n = 0)
    (h_i : σ * τ * ‖L‖ ^ 2 < 1)
    (h_ii : ∀ n, 0 < ρ n ∧ ρ n < 2)
    (h_iii : Tendsto (fun N => ∑ n ∈ Finset.range N, ρ n * (2 - ρ n)) atTop atTop)
    (h_iv : Summable (fun n => ρ n * ‖eG n‖) ∧ Summable (fun n => ρ n * ‖eH n‖)) :
    (∀ (x : ℕ → X) (y : ℕ → Y), IsAlg31Run F L τ σ PG PH ρ eF eG eH x y →
      ∃ (xh : X) (yh : Y), IsPDSolution F G H L xh yh ∧
        ThreeOpSplitting.Convergence.WeakTendsto x xh ∧
        ThreeOpSplitting.Convergence.WeakTendsto y yh) ∧
    (∀ (x : ℕ → X) (y : ℕ → Y), IsAlg32Run F L τ σ PG PH ρ eF eG eH x y →
      ∃ (xh : X) (yh : Y), IsPDSolution F G H L xh yh ∧
        ThreeOpSplitting.Convergence.WeakTendsto x xh ∧
        ThreeOpSplitting.Convergence.WeakTendsto y yh) := by sorry

end CondatPD.PPA
