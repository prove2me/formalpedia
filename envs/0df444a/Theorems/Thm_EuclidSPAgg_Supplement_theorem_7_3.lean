-- Prove2me | Theorems.Thm_EuclidSPAgg_Supplement_theorem_7_3
-- name    : EuclidSPAgg.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:46:12.733357+00:00
-- url     : https://prove2.me/theorems/ab386ba4-58de-4ffe-8fae-4bb84fce6a9e
-- title:
--   Theorem 7.3 — rigidity of anonymous, unanimous, translation-equivariant strategyproof mechanisms with bounded influence
-- statement:
--   Let $n\ge3$ and $d\ge1$, and let $E=\mathbb R^d$. A mechanism $f:E^n\to E$ is anonymous, unanimous, translation-equivariant, strategyproof, and has bounded individual influence (every unilateral menu is bounded) if and only if there are an orthonormal basis $\mathcal B=(e_1,\dots,e_d)$ of $E$ and fixed ranks $k_j\in\{2,\dots,n-1\}$ such that
--   $$
--   f=Q_{\mathcal B,k},\qquad Q_{\mathcal B,k}(x)=\sum_{j=1}^d x_{(k_j),j}\,e_j ,
--   $$
--   where $x_{(r),j}$ is the $r$-th smallest of $\langle e_j,x_1\rangle,\dots,\langle e_j,x_n\rangle$.
--
--   This is the paper's final characterization: unlike the continuous rigidity theorem (Theorem 6.6), no continuity is assumed, and both directions are asserted.
--
--   Differences from the source:
--   - encoding: ranks $k_j\in\{2,\dots,n-1\}$ (1-based) → 0-based indices $k_j$ with $1\le k_j$ and $k_j+2\le n$; reason: the published rule $Q$ uses 0-based ranks; same rules.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Theorem 7.3, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
import Definitions.Def_EuclidSPAgg_IsAnonymous
import Definitions.Def_EuclidSPAgg_IsUnanimous
import Definitions.Def_EuclidSPAgg_IsTranslationEquivariant
import Definitions.Def_EuclidSPAgg_HasBoundedInfluence
import Definitions.Def_EuclidSPAgg_Q
open RBMSensitivity (E)

namespace EuclidSPAgg.Supplement

open EuclidSPAgg

/-- **Theorem 7.3** (rigidity; Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.32 (PDF p.34)). Let `n ≥ 3` and `d ≥ 1`. A mechanism
`f : Eⁿ → E` is anonymous, unanimous, translation-equivariant, strategyproof, and has bounded
individual influence if and only if there are an orthonormal basis `B` and fixed ranks
`k_j ∈ {2, …, n − 1}` such that `f = Q_{B,k}`.

**Formalization Note** No continuity is assumed on the left. Ranks are 0-based, as in the published
`Q`: the paper's rank `k_j ∈ {2, …, n − 1}` is the index `k j` with `1 ≤ k j` and `k j + 2 ≤ n`. -/
theorem theorem_7_3 (n d : ℕ) (hn : 3 ≤ n) (hd : 1 ≤ d) (f : Mech n d) :
    (IsAnonymous f ∧ IsUnanimous f ∧ IsTranslationEquivariant f ∧ IsStrategyproof f ∧
        HasBoundedInfluence f) ↔
      ∃ (B : OrthonormalBasis (Fin d) ℝ (E d)) (k : Fin d → Fin n),
        (∀ j, 1 ≤ (k j : ℕ) ∧ (k j : ℕ) + 2 ≤ n) ∧ f = Q B k := by sorry

end EuclidSPAgg.Supplement
