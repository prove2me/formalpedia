-- Prove2me | Theorems.Thm_DeltaSLearning_lemma_1
-- name    : DeltaSLearning.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:07:45.057+00:00
-- url     : https://prove2.me/theorems/422ec185-3eb2-4f15-935e-115ae5224b52
-- title:
--   Lemma 1 — $|\tilde C_t|\le\gamma$
-- statement:
--   For every period of the inventory system under any feasible policy, the pseudo cost (7) is bounded:
--   $$|\tilde C_t|\le\gamma=K+(h+c+p)\beta .$$
--   Stated pathwise: for all $x,y,d$ with $0\le x\le y\le\beta$ and $d\ge0$, $|K\mathbf 1(y>x)+c(y-x)+h(y-d)^+-p\min(y,d)|\le\gamma$.
--
--   It gives $|G(\delta,S)|\le\gamma L(\delta)$ and $|V(\delta,S)|\le\gamma$, which every later estimate uses.
--
--   Differences from the source:
--   - generalization: |C̃_t| ≤ γ for all periods t ≥ 1 of the system → |C̃(x, y, d)| ≤ γ for all x, y, d with 0 ≤ x ≤ y ≤ β and d ≥ 0; reason: every period of every feasible policy has 0 ≤ x_t ≤ y_t ≤ β and d_t ≥ 0, so this specializes to the source
--   - reading: c and h are per-unit ordering and holding costs, sign not stated (p.7) → c ≥ 0 and h > 0; reason: costs are nonnegative; (19) divides by h, and for c < 0 the bound γ of (10) can be negative, so Lemma 1 would fail
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Lemma 1, eq. (10), p.12

import Mathlib
import Definitions.Def_DeltaSLearning_pseudoCost
import Definitions.Def_DeltaSLearning_gamma

namespace DeltaSLearning

/-- **Lemma 1.** The pseudo cost of every period satisfies `|C̃_t| ≤ γ = K + (h + c + p)β`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Lemma 1 and eq. (10), p.12.

**Formalization Note** Stated pathwise for one period: for every beginning inventory `x`,
after-order level `y` and demand `d` with `0 ≤ x ≤ y ≤ β` and `d ≥ 0`. Every period of every
feasible policy has such values (`x_t = (y_{t-1} - d_{t-1})⁺ ≥ 0`, `y_t ≥ x_t`, `y_t ≤ β`). -/
theorem lemma_1 (cp : Params) (x y d : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ cp.β)
    (hd : 0 ≤ d) : |pseudoCost cp x y d| ≤ gamma cp := by sorry

end DeltaSLearning
