-- Prove2me | Theorems.Thm_EuclidSPAgg_corollary_7_2
-- name    : EuclidSPAgg.corollary_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:43:43.109568+00:00
-- url     : https://prove2.me/theorems/dcaea40b-31c7-4d77-9c3d-a6fdca2e7bda
-- title:
--   Corollary 7.2 — unanimous strategyproof mechanisms are continuous; finite-ratio ones are unanimous and $\ell_1$-Lipschitz
-- statement:
--   1. Every unanimous deterministic strategyproof mechanism $f:E^n\to E$ is continuous.
--   2. For $n\ge2$, every strategyproof $f$ with $\mathrm{AR}(f)<\infty$ is unanimous and satisfies
--   $$
--   \|f(x)-f(x')\|\le\sum_{i=1}^n\|x_i-x'_i\|\qquad\text{for all profiles }x,x'. \tag{7.1}
--   $$
--   3. In particular, for $n\ge2$, every anonymous strategyproof mechanism with finite ratio belongs to $\mathcal F_{n,d}$.
--
--   This places every relevant competitor of the coordinate-wise median inside the continuous class.
--
--   Differences from the source: none.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Corollary 7.2, p.32 (PDF p.34); display (7.1), p.31 (PDF p.33)

import Mathlib
import Definitions.Def_EuclidSPAgg_InF
import Definitions.Def_EuclidSPAgg_AR
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Corollary 7.2** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.32 (PDF p.34)). Every unanimous deterministic strategyproof mechanism
is continuous. For `n ≥ 2`, every `f ∈ S_{n,d}` with `AR(f) < ∞` is unanimous and satisfies (7.1).
In particular, every finite-ratio member of `A_{n,d}` belongs to `F_{n,d}`.

Display (7.1) (p.31) is `‖f(x) − f(x′)‖ ≤ ∑ᵢ ‖xᵢ − x′ᵢ‖` for all profiles `x, x′`.

**Formalization Note** The three sentences are the three conjuncts; the last two carry `2 ≤ n`.
`n ≥ 1` and `d ≥ 1` are the paper's standing assumptions (p.8). -/
theorem corollary_7_2 (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    (∀ f : Mech n d, IsStrategyproof f → IsUnanimous f → Continuous f) ∧
    (2 ≤ n → ∀ f : Mech n d, IsStrategyproof f → AR f < ⊤ →
      IsUnanimous f ∧ ∀ x x' : Fin n → E d, ‖f x - f x'‖ ≤ ∑ i, ‖x i - x' i‖) ∧
    (2 ≤ n → ∀ f : Mech n d, IsStrategyproof f → IsAnonymous f → AR f < ⊤ → InF f) := by sorry

end EuclidSPAgg
