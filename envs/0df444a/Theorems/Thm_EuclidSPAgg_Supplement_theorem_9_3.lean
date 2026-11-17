-- Prove2me | Theorems.Thm_EuclidSPAgg_Supplement_theorem_9_3
-- name    : EuclidSPAgg.Supplement.theorem_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:47:46.669931+00:00
-- url     : https://prove2.me/theorems/73c5b002-e655-4039-8387-e1731dd9683b
-- title:
--   Theorem 9.3 — large-population optimality, $\lim_{n\to\infty}a_{n,d}=C_d$
-- statement:
--   Fix $d\ge1$. Let $a_{n,d}=\inf_{f\in\mathcal S_{n,d}}\mathrm{AR}(f)$ be the optimal ratio of deterministic strategyproof mechanisms on $n$ agents in $\mathbb R^d$, and let $C_d=\sup_{n\ge2}R_{n,d}$, where $R_{n,d}$ is the ratio of the coordinate-wise median. Then
--   $$
--   \lim_{n\to\infty}a_{n,d}=C_d .
--   $$
--   Equivalently:
--
--   1. every sequence of mechanisms $f_n\in\mathcal S_{n,d}$ satisfies $\liminf_{n\to\infty}\mathrm{AR}(f_n)\ge C_d$;
--   2. $\displaystyle\inf_{(f_n):\,f_n\in\mathcal S_{n,d}}\ \sup_{n\ge2}\mathrm{AR}(f_n)=C_d$.
--
--   No anonymity or continuity is assumed of the competitors: asymptotically, no deterministic strategyproof mechanism beats the coordinate-wise median.
--
--   Differences from the source:
--   - encoding: the limit and its two "equivalent" forms → the conjunction of all three statements; reason: the paper asserts each of them.
--   - encoding: a sequence $f_n\in\mathcal S_{n,d}$ → a family $(f_n)_{n\in\mathbb N}$ strategyproof for every $n\ge2$; reason: the values at $n=0,1$ affect neither the limit inferior nor $\sup_{n\ge2}$.
--   - encoding: $a_{n,d}$, $C_d$, $\mathrm{AR}$ → valued in $[0,\infty]$; reason: ratios may be infinite.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Theorem 9.3, p.37 (PDF p.39); display (2.2), p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EuclidSPAgg_Supplement_optRatio
import Definitions.Def_EuclidSPAgg_Supplement_medianRatioSup
open RBMSensitivity (E)
open Filter Topology

namespace EuclidSPAgg.Supplement

open EuclidSPAgg

/-- **Theorem 9.3** (large-population optimality; Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.37 (PDF p.39)). For every fixed finite
`d ≥ 1`, `lim_{n→∞} a_{n,d} = C_d`. Equivalently, every sequence `f_n ∈ S_{n,d}` satisfies
`liminf_{n→∞} AR(f_n) ≥ C_d`, and `inf_{(f_n) : f_n ∈ S_{n,d}} sup_{n ≥ 2} AR(f_n) = C_d`.

**Formalization Note** All three printed clauses are asserted, as a conjunction. `a_{n,d}` is
`optRatio n d` and `C_d = sup_{n≥2} R_{n,d}` is `medianRatioSup d`, both in `ℝ≥0∞`. A sequence is a
family `f : (n : ℕ) → Mech n d`, required to be strategyproof for `n ≥ 2` (the range of the
supremum; the values at `n = 0, 1` affect neither a `liminf` nor `sup_{n≥2}`). Competitors carry no
anonymity or continuity hypothesis. -/
theorem theorem_9_3 (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n => optRatio n d) atTop (𝓝 (medianRatioSup d)) ∧
    (∀ f : (n : ℕ) → Mech n d, (∀ n, 2 ≤ n → IsStrategyproof (f n)) →
        medianRatioSup d ≤ liminf (fun n => AR (f n)) atTop) ∧
    (⨅ (f : (n : ℕ) → Mech n d) (_ : ∀ n, 2 ≤ n → IsStrategyproof (f n)),
        ⨆ (n : ℕ) (_ : 2 ≤ n), AR (f n)) = medianRatioSup d := by sorry

end EuclidSPAgg.Supplement
