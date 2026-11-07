-- Prove2me | Theorems.Thm_EuclidSPAgg_lemma_8_2
-- name    : EuclidSPAgg.lemma_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:43:09.027517+00:00
-- url     : https://prove2.me/theorems/f43d9524-8619-43ca-a039-ea59ca9cae26
-- title:
--   Lemma 8.2 — a ratio $R<n-1$ bounds every unilateral menu, display (8.1); menus are compact
-- statement:
--   Let $n\ge2$ and let $f:E^n\to E$ be strategyproof with approximation ratio $R<n-1$. Fix the reports $z_1,\dots,z_{n-1}$ of all agents except one. If $y$ belongs to the remaining agent's unilateral menu, then for every $b\in E$
--   $$
--   \|y-b\|\le\frac{R+1}{n-1-R}\sum_{j=1}^{n-1}\|z_j-b\|. \tag{8.1}
--   $$
--   Consequently, every unilateral menu of $f$ is compact.
--
--   This turns an approximation guarantee into bounded individual influence.
--
--   **Formalization Note** For $n=2$ the hypothesis $R<1$ cannot hold, because every ratio is at least $1$; the source has the same vacuous case.
--
--   Differences from the source:
--   - encoding: f has approximation ratio R < n − 1 → R : ℝ with AR f = ENNReal.ofReal R and R < n − 1; reason: the ratio is a finite number R
--   - encoding: the reports z_1, …, z_{n−1} of all agents except one → the reports x j, j ≠ i, of a profile x, summed over Finset.univ.erase i; reason: the remaining agent is any i, and its own entry of x is ignored by the menu
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Lemma 8.2, display (8.1), p.33 (PDF p.35)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
import Definitions.Def_EuclidSPAgg_menu
import Definitions.Def_EuclidSPAgg_AR
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Lemma 8.2** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.33 (PDF p.35)). Let `n ≥ 2`, and let `f ∈ S_{n,d}` have approximation
ratio `R < n − 1`. Fix the reports `z₁, …, z_{n−1}` of all agents except one. If `y` belongs to the
remaining agent's unilateral menu, then, for every `b ∈ E`,
`‖y − b‖ ≤ (R + 1)/(n − 1 − R) · ∑_{j=1}^{n−1} ‖z_j − b‖` (display (8.1)).
Consequently, every unilateral menu of `f` is compact.

**Formalization Note** "Approximation ratio `R`" is `AR f = ENNReal.ofReal R` with `R : ℝ`
(so the ratio is finite). The remaining agent is any `i`, and `z₁, …, z_{n−1}` are the reports
`x j`, `j ≠ i` (the sum over `Finset.univ.erase i`); `x i` is ignored by `menu f i x`. For `n = 2`
the hypothesis `R < 1` cannot hold, since every ratio is at least one; the page has the same
vacuous case. `d ≥ 1` is standing (p.8). -/
theorem lemma_8_2 (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) (f : Mech n d) (hSP : IsStrategyproof f)
    (R : ℝ) (hAR : AR f = ENNReal.ofReal R) (hR : R < (n : ℝ) - 1) :
    (∀ (i : Fin n) (x : Fin n → E d) (y : E d), y ∈ menu f i x → ∀ b : E d,
        ‖y - b‖ ≤ (R + 1) / ((n : ℝ) - 1 - R) * ∑ j ∈ Finset.univ.erase i, ‖x j - b‖) ∧
      ∀ (i : Fin n) (x : Fin n → E d), IsCompact (menu f i x) := by sorry

end EuclidSPAgg
