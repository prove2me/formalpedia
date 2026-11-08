-- Prove2me | Theorems.Thm_FairFacilityLoc_proposition_3_11
-- name    : FairFacilityLoc.proposition_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:13:13.343082+00:00
-- url     : https://prove2.me/theorems/ce9cc3f7-fe1e-4437-a2f4-3adfbc8f459c
-- title:
--   Proposition 3.11 — the scores bound the side-length gap
-- statement:
--   Let $z\ge0$ with $\|z\|_2=1$, let $x$ be a profile and let $a$ be a nonnegative weight vector. For $d\in\{1,3\}$,
--   $$L^+(a)^2-L^-(a)^2\le\bar Q(a),$$
--   and for $d=2$, for a coordinate $r^*$ with the largest entry,
--   $$L^+(a)^2-L^-(a)^2\le\max\{Q_{r^*}(a),\bar Q(a)\}.$$
--
--   Together with Lemma 3.9 it bounds the side-length gap by the capacities. The maximum at $d=2$ is necessary: the weighted score alone fails (Remark 3.14).
--
--   Differences from the source:
--   - generalization: a linear group with weight $w_j$ → a nonnegative weight vector $a\in\mathbb R^N$; reason: the proof of Proposition 3.27 (p.48) re-runs this statement for weight vectors; a linear group is $a=w_j\mathbf 1_{G_j}$
--   - generalization: normalized coordinates of a mechanism output → any profile and any $z\ge0$ with $\|z\|_2=1$; reason: the proof uses only $z\ge0$ and $\|z\|_2=1$
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Proposition 3.11, p.28 (PDF p.30); family form p.48 (PDF p.50)

import Mathlib
import Definitions.Def_FairFacilityLoc_penalty
import Definitions.Def_FairFacilityLoc_sideLength
import Definitions.Def_FairFacilityLoc_capacity

namespace FairFacilityLoc

/-- **Proposition 3.11** (Yan, Zhou, manuscript, sha256 642a1268…, p.28, PDF p.30). For `d ∈ {1, 3}`,
`(L⁺(a))² − (L⁻(a))² ≤ Q̄(a)`. For `d = 2`, `(L⁺(a))² − (L⁻(a))² ≤ max{Q_{r*}(a), Q̄(a)}`.

**Formalization Note.** Stated for a nonnegative weight vector, as p.48 applies it; a linear group is
`a = w_j 1_{G_j}`. Needs only `z ≥ 0`, `∥z∥₂ = 1` and any profile. The `max` at `d = 2` is what the page prints:
Remark 3.14 shows the weighted score alone fails. -/
theorem proposition_3_11 {n d : ℕ} (x : Fin n → GeoSemialgCSP.E d) (z : GeoSemialgCSP.E d) (hz : ∀ r, 0 ≤ z r) (hz1 : ‖z‖ = 1)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ((d = 1 ∨ d = 3) →
        posLength x z a ^ 2 - nonposLength x z a ^ 2 ≤ weightedScore (penalty d) x z a) ∧
      (d = 2 → ∀ rs, IsTopCoord z rs →
        posLength x z a ^ 2 - nonposLength x z a ^ 2 ≤
          max (posScore (penalty d) x a rs) (weightedScore (penalty d) x z a)) := by sorry

end FairFacilityLoc
