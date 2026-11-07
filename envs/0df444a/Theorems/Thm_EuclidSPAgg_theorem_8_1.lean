-- Prove2me | Theorems.Thm_EuclidSPAgg_theorem_8_1
-- name    : EuclidSPAgg.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:43:06.379207+00:00
-- url     : https://prove2.me/theorems/c83ca796-e33a-450a-a1b5-3977ae6d6a0c
-- title:
--   Theorem 8.1 — normalization: every member of $\mathcal F_{n,d}$ has a normalized member with no larger ratio
-- statement:
--   For every $n\ge2$, $d\ge1$ and $f\in\mathcal F_{n,d}$, there is a normalized (translation-equivariant and positively homogeneous) mechanism $\bar f\in\mathcal F_{n,d}$ such that
--   $$
--   \mathrm{AR}(\bar f)\le\mathrm{AR}(f).
--   $$
--
--   This brings every competitor into the scope of the rigidity theorem, which requires translation equivariance.
--
--   **Formalization Note** Ratios are extended reals; $\mathrm{AR}(f)=\infty$ is allowed.
--
--   Differences from the source: none.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Theorem 8.1, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_EuclidSPAgg_InF
import Definitions.Def_EuclidSPAgg_IsNormalized
import Definitions.Def_EuclidSPAgg_AR
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Theorem 8.1** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.33 (PDF p.35)). For every `n ≥ 2`, `d ≥ 1` and `f ∈ F_{n,d}`, there is
a normalized mechanism `f̄ ∈ F_{n,d}` such that `AR(f̄) ≤ AR(f)`.

**Formalization Note** `AR` is valued in `ℝ≥0∞`; `AR f = ⊤` is allowed, as in the paper. -/
theorem theorem_8_1 (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) (f : Mech n d) (hf : InF f) :
    ∃ fbar : Mech n d, InF fbar ∧ IsNormalized fbar ∧ AR fbar ≤ AR f := by sorry

end EuclidSPAgg
