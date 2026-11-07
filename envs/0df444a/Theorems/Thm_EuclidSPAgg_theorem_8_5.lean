-- Prove2me | Theorems.Thm_EuclidSPAgg_theorem_8_5
-- name    : EuclidSPAgg.theorem_8_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:17.883841+00:00
-- url     : https://prove2.me/theorems/bea8e092-2fe1-4fbf-9207-ab36a59ed520
-- title:
--   Theorem 8.5 — anonymous median optimality: $\inf_{f\in\mathcal A_{n,d}}\mathrm{AR}(f)=R_{n,d}$ for $n\ge3$, $d\ge1$
-- statement:
--   For every $n\ge3$ and every $d\ge1$,
--   $$
--   \inf_{f\in\mathcal A_{n,d}}\mathrm{AR}(f)=R_{n,d}=\mathrm{AR}(\mathrm{CM}_{n,d}),
--   $$
--   where $\mathcal A_{n,d}$ is the class of all anonymous deterministic strategyproof mechanisms $f:(\mathbb R^d)^n\to\mathbb R^d$ and $\mathrm{AR}$ is the worst-case ratio of social cost to optimal social cost.
--
--   No anonymous strategyproof mechanism has a smaller approximation ratio than the coordinate-wise median, for every population of at least three agents and every finite dimension. The competitors are arbitrary: no continuity, unanimity, translation equivariance or finite ratio is assumed.
--
--   **Formalization Note** The infimum is taken in $[0,\infty]$.
--
--   Differences from the source: none.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Theorem 8.5, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_EuclidSPAgg_InA
import Definitions.Def_EuclidSPAgg_medianRatio
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Theorem 8.5** (anonymous median optimality; Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.35 (PDF p.37)). For every `n ≥ 3` and
`d ≥ 1`, `inf_{f ∈ A_{n,d}} AR(f) = R_{n,d}`.

**Formalization Note** The infimum is in `ℝ≥0∞` over all anonymous deterministic strategyproof maps
`f : (ℝᵈ)ⁿ → ℝᵈ` (`InA f`), with no continuity, unanimity, translation-equivariance or
finite-ratio hypothesis on the competitors. `R_{n,d} = AR(CM_{n,d})` is `medianRatio n d`. -/
theorem theorem_8_5 (n d : ℕ) (hn : 3 ≤ n) (hd : 1 ≤ d) :
    ⨅ (f : Mech n d) (_ : InA f), AR f = medianRatio n d := by sorry

end EuclidSPAgg
