-- Prove2me | Theorems.Thm_ApproachRegret_Calibration_algorithm3_oracle
-- name    : ApproachRegret.Calibration.algorithm3_oracle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T15:45:41.808924+00:00
-- url     : https://prove2.me/theorems/9f4ebe0c-59c2-409b-b403-89ab81d5d31a
-- title:
--   Algorithm 3 — the oracle returns $w\in\Delta_{m+1}$ with $\langle u(w,y),\theta\rangle\le\varepsilon/2$ for every $y$
-- statement:
--   Let $m\ge1$, $\varepsilon=1/m$, and let $\theta\in\mathbb R^{m+1}$ with $\|\theta\|_\infty\le1$. Then:
--
--   1. Algorithm 3 returns some $w$ on input $\theta$;
--   2. every output $w$ of Algorithm 3 on $\theta$ is a probability vector, $w\in\Delta_{m+1}$, and for every outcome $y\in[0,1]$,
--   $$\bigl\langle u(w,y),\theta\bigr\rangle=\sum_{i=0}^m\theta(i)\,w(i)\Bigl(y-\frac im\Bigr)\ \le\ \frac\varepsilon2 .$$
--
--   This is the halfspace oracle of the reduction: for every direction $\theta$ in the cube it produces a mixed forecast whose payoff lies in the halfspace $\{z:\langle z,\theta\rangle\le\varepsilon/2\}$ whatever the outcome.
--
--   **Formalization Note** The paper's header "$\mathcal O:w\mapsto\theta$" is read as $\theta\mapsto w$, "$\ell(w,y)$" as $u(w,y)$, "$\theta(1)\le0$" in the verification as $\theta(0)\le0$, and the sum $\sum_{i=1}^m$ as running over $i=0,\dots,m$. The paper checks $y\in\{0,1\}$; the statement covers the game's outcome set $[0,1]$ (p. 41). The existence clause rules out a vacuous guarantee.
-- source:
--   Abernethy, Bartlett, Hazan (COLT 2011, JMLR W&CP 19), Algorithm 3 and Constructing the Oracle, p. 43

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game
import Definitions.Def_ApproachRegret_Calibration_Algorithms

namespace ApproachRegret.Calibration

/-- Algorithm 3 and its check (p. 43): for `m ≥ 1` and every `θ ∈ B∞(1) ⊂ ℝ^{m+1}`, Algorithm 3
returns some `w`, and every output `w` is a distribution in `Δ_{m+1}` with
`⟨u(w, y), θ⟩ ≤ ε/2 = 1/(2m)` for every outcome `y ∈ [0, 1]`. -/
theorem algorithm3_oracle (m : ℕ) (hm : 1 ≤ m) (θ : ApproachRegret.ToOLO.E (m + 1)) (hθ : θ ∈ cube (m + 1)) :
    (∃ w, IsAlg3Output m θ w) ∧
      ∀ w, IsAlg3Output m θ w →
        w ∈ stdSimplex ℝ (Fin (m + 1)) ∧
          ∀ y ∈ Set.Icc (0 : ℝ) 1, inner ℝ (payoff m w y) θ ≤ eps m / 2 := by sorry

end ApproachRegret.Calibration
