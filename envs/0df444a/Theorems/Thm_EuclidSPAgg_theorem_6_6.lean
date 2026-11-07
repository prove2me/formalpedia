-- Prove2me | Theorems.Thm_EuclidSPAgg_theorem_6_6
-- name    : EuclidSPAgg.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:43:05.141734+00:00
-- url     : https://prove2.me/theorems/388ac611-da27-4512-9017-fc2fb5ccd52a
-- title:
--   Theorem 6.6 — continuous rigidity: a translation-equivariant member of $\mathcal F_{n,d}$ with bounded menus is $Q_{\mathcal B,k}$ with interior ranks
-- statement:
--   Let $n\ge3$, $d\ge1$, and let $f\in\mathcal F_{n,d}$ be translation-equivariant. If every unilateral menu of $f$ is bounded, then there are one orthonormal basis $\mathcal B$ and fixed ranks $k_j\in\{2,\dots,n-1\}$ such that
--   $$
--   f=Q_{\mathcal B,k}.
--   $$
--
--   This is the rigidity theorem for continuous mechanisms; the median-optimality proof applies it to the normalized representative of a competitor.
--
--   **Formalization Note** Ranks are 0-based: rank $k_j\in\{2,\dots,n-1\}$ is a Lean index between $1$ and $n-2$.
--
--   Differences from the source:
--   - encoding: k_j ∈ {2, …, n − 1} → k : Fin d → Fin n with 1 ≤ k j and k j + 2 ≤ n; reason: 0-based ranks; the same set of rank vectors
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Theorem 6.6, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_EuclidSPAgg_InF
import Definitions.Def_EuclidSPAgg_IsTranslationEquivariant
import Definitions.Def_EuclidSPAgg_HasBoundedInfluence
import Definitions.Def_EuclidSPAgg_Q
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Theorem 6.6** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.30 (PDF p.32)). Let `n ≥ 3`, `d ≥ 1`, and let `f ∈ F_{n,d}` be
translation-equivariant. If every unilateral menu of `f` is bounded, then there are one orthonormal
basis `B` and fixed ranks `k_j ∈ {2, …, n − 1}` such that `f = Q_{B,k}`.

**Formalization Note** Ranks are 0-based: rank `k_j ∈ {2, …, n − 1}` is the index `k j` with
`1 ≤ k j` and `k j + 2 ≤ n`. -/
theorem theorem_6_6 (n d : ℕ) (hn : 3 ≤ n) (hd : 1 ≤ d) (f : Mech n d) (hF : InF f)
    (hT : IsTranslationEquivariant f) (hBI : HasBoundedInfluence f) :
    ∃ (B : OrthonormalBasis (Fin d) ℝ (E d)) (k : Fin d → Fin n),
      (∀ j, 1 ≤ (k j : ℕ) ∧ (k j : ℕ) + 2 ≤ n) ∧ f = Q B k := by sorry

end EuclidSPAgg
