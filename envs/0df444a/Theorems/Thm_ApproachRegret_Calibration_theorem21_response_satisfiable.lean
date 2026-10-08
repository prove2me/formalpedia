-- Prove2me | Theorems.Thm_ApproachRegret_Calibration_theorem21_response_satisfiable
-- name    : ApproachRegret.Calibration.theorem21_response_satisfiable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T15:29:05.279+00:00
-- url     : https://prove2.me/theorems/8cd4a966-0681-4589-9be2-791f0b22e6ef
-- title:
--   Theorem 21 — $B_1(\varepsilon/2)$ is response-satisfiable and approachable for the calibration game (11)
-- statement:
--   Let $m\ge1$ and $\varepsilon=1/m$, and consider the vector-valued game (11) with player set $\mathcal X=\Delta_{m+1}$, adversary set $\mathcal Y=[0,1]$ and payoff $u(w,y)(i)=w(i)(y-i/m)$, $i=0,\dots,m$. The set $S=B_1(\varepsilon/2)=\{z\in\mathbb R^{m+1}:\|z\|_1\le\varepsilon/2\}$ is
--
--   1. **response-satisfiable**: for every outcome $y\in[0,1]$ there is a distribution $w\in\Delta_{m+1}$ with
--   $$u(w,y)\in B_1(\varepsilon/2),\qquad\text{i.e.}\qquad \sum_{i=0}^m\Bigl|w(i)\Bigl(y-\frac im\Bigr)\Bigr|\le\frac\varepsilon2 ;$$
--   2. and, hence, **approachable**: there is an algorithm $\mathcal A$ that chooses $w_t=\mathcal A(y_1,\dots,y_{t-1})\in\Delta_{m+1}$ in round $t=1,2,\dots$ such that, for every sequence $y_1,y_2,\dots\in[0,1]$,
--   $$\mathtt{dist}\Bigl(\frac1T\sum_{t=1}^T u(w_t,y_t),\,B_1(\varepsilon/2)\Bigr)\to0\qquad(T\to\infty).$$
--
--   Approachability of $B_1(\varepsilon/2)$ is what makes a forecaster drawing its predictions from $w_t$ calibrated (Lemma 20).
--
--   **Formalization Note** Response-satisfiability and approachability are those of Definitions 4 and 5 (p. 31). An algorithm is a deterministic map from the history $(y_1,\dots,y_{t-1})$, indexed by `Fin (t-1)`, to $\Delta_{m+1}$; rounds are $t=1,2,\dots$ and `A (t-1)` is called in round $t$. $\mathtt{dist}$ is the Euclidean distance (`Metric.infDist` in `EuclideanSpace ℝ (Fin (m+1))`); since all norms on $\mathbb R^{m+1}$ are equivalent, convergence to $0$ does not depend on that choice. The paper derives approachability from Blackwell's theorem (Theorem 6), which it cites; the statement here asks for the approachability conclusion itself. The paper's proof writes $y-i/m\in[-1/m,1/m]$; for the nearest grid point the bound is $[-1/(2m),1/(2m)]$, which is what the statement needs.
-- source:
--   Abernethy, Bartlett, Hazan (COLT 2011, JMLR W&CP 19), Theorem 21, p. 41

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game

namespace ApproachRegret.Calibration

/-- Theorem 21 (p. 41): for the game (11) with `ε = 1/m`, `m ≥ 1`, `X = Δ_{m+1}`, `Y = [0, 1]`,
the set `S = B₁(ε/2)` is
1. response-satisfiable (Definition 4, p. 31): for every outcome `y ∈ [0, 1]` there is
   `w ∈ Δ_{m+1}` with `u(w, y) ∈ B₁(ε/2)`; and, hence,
2. approachable (Definition 5, p. 31): some algorithm `A`, choosing `w_t ∈ Δ_{m+1}` in round
   `t = 1, 2, …` from the past outcomes `y₁, …, y_{t−1}` (`w_t = A (t − 1) (y₁, …, y_{t−1})`),
   makes the Euclidean distance `dist((1/T) ∑_{t=1}^T u(w_t, y_t), B₁(ε/2))` tend to `0` as
   `T → ∞`, for every outcome sequence `y₁, y₂, … ∈ [0, 1]`. -/
theorem theorem21_response_satisfiable (m : ℕ) (hm : 1 ≤ m) :
    (∀ y ∈ Set.Icc (0 : ℝ) 1, ∃ w ∈ stdSimplex ℝ (Fin (m + 1)),
      payoff m w y ∈ l1Ball (m + 1) (eps m / 2)) ∧
    ∃ A : (t : ℕ) → (Fin t → ℝ) → (Fin (m + 1) → ℝ),
      (∀ t (h : Fin t → ℝ), A t h ∈ stdSimplex ℝ (Fin (m + 1))) ∧
      ∀ y : ℕ → ℝ, (∀ t, 1 ≤ t → y t ∈ Set.Icc (0 : ℝ) 1) →
        Filter.Tendsto
          (fun T : ℕ => Metric.infDist
            (avgPayoff m T (fun t => A (t - 1) (fun j => y (j.val + 1))) y)
            (l1Ball (m + 1) (eps m / 2)))
          Filter.atTop (nhds 0) := by sorry

end ApproachRegret.Calibration
