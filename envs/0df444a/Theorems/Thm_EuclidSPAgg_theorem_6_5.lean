-- Prove2me | Theorems.Thm_EuclidSPAgg_theorem_6_5
-- name    : EuclidSPAgg.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:42:55.857228+00:00
-- url     : https://prove2.me/theorems/c2ae1bb8-bc03-47f5-af07-1120e758cb5b
-- title:
--   Theorem 6.5 — a normalized member of $\mathcal F_{m,d}$ with box-shaped menus is a fixed-frame order-statistic rule
-- statement:
--   Let $m\ge1$ and let $F\in\mathcal F_{m,d}$ be normalized. Suppose every unilateral menu of $F$ is an orthogonal box, where the frame may depend on the menu. Then there are one orthonormal basis $\mathcal B$ and fixed ranks $k_j\in\{1,\dots,m\}$ such that
--   $$
--   F=Q_{\mathcal B,k}.
--   $$
--
--   The theorem aligns the menu frames into one frame and fixes the ranks; it is the induction that classifies the absorbing mechanism.
--
--   **Formalization Note** Ranks are 0-based, so every rank vector in $\{1,\dots,m\}^d$ is representable. The hypothesis allows a different frame for each menu; the conclusion has one frame for all profiles.
--
--   Differences from the source:
--   - encoding: k_j ∈ {1, …, m} → k : Fin d → Fin m; reason: 0-based ranks; the same set of rank vectors
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Theorem 6.5, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_EuclidSPAgg_InF
import Definitions.Def_EuclidSPAgg_IsNormalized
import Definitions.Def_EuclidSPAgg_menu
import Definitions.Def_EuclidSPAgg_Q
import Definitions.Def_EuclidSPAgg_IsOrthogonalBox
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Theorem 6.5** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.29 (PDF p.31)). Let `m ≥ 1`, and let `F ∈ F_{m,d}` be normalized.
Suppose every unilateral menu of `F` is an orthogonal box, where the frame may depend on the menu.
Then there are one orthonormal basis `B` and fixed ranks `k_j ∈ {1, …, m}` such that `F = Q_{B,k}`.

**Formalization Note** Ranks are 0-based, `k : Fin d → Fin m`, which is exactly
`k_j ∈ {1, …, m}`. The hypothesis has the frame inside `IsOrthogonalBox` (per menu); the
conclusion has one `B` for all profiles. `d ≥ 1` is standing (p.8). -/
theorem theorem_6_5 (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (F : Mech m d) (hF : InF F)
    (hN : IsNormalized F) (hbox : ∀ (i : Fin m) (z : Fin m → E d), IsOrthogonalBox (menu F i z)) :
    ∃ (B : OrthonormalBasis (Fin d) ℝ (E d)) (k : Fin d → Fin m), F = Q B k := by sorry

end EuclidSPAgg
