-- Prove2me | Theorems.Thm_EuclidSPAgg_corollary_8_3
-- name    : EuclidSPAgg.corollary_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:43:31.423194+00:00
-- url     : https://prove2.me/theorems/960b0016-8624-4784-9ee6-bda3b9734574
-- title:
--   Corollary 8.3 — an anonymous mechanism with ratio below $n-1$ is beaten or matched by a fixed-rank rule with interior ranks
-- statement:
--   Let $n\ge3$ and let $f\in\mathcal A_{n,d}$ (anonymous and strategyproof) satisfy $\mathrm{AR}(f)<n-1$. Then there are an orthonormal frame $\mathcal B$ and fixed ranks $k_j\in\{2,\dots,n-1\}$ such that
--   $$
--   \mathrm{AR}(Q_{\mathcal B,k})\le\mathrm{AR}(f).
--   $$
--   The rule $Q_{\mathcal B,k}$ can be chosen as the normalized representative from Theorem 8.1: it is a normalized member of $\mathcal F_{n,d}$.
--
--   This reduces the optimality question to fixed-rank rules.
--
--   **Formalization Note** Ranks are 0-based (indices between $1$ and $n-2$).
--
--   Differences from the source:
--   - encoding: k_j ∈ {2, …, n − 1} → k : Fin d → Fin n with 1 ≤ k j and k j + 2 ≤ n; reason: 0-based ranks; the same set of rank vectors
--   - reading: Q_{B,k} can be chosen as the normalized representative from Theorem 8.1 → Q B k ∈ F_{n,d} and Q B k is normalized (with AR (Q B k) ≤ AR f); reason: Theorem 8.1 is an existence statement; its representatives are exactly the normalized members of F_{n,d} with ratio at most AR f
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Corollary 8.3, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_EuclidSPAgg_InA
import Definitions.Def_EuclidSPAgg_InF
import Definitions.Def_EuclidSPAgg_IsNormalized
import Definitions.Def_EuclidSPAgg_AR
import Definitions.Def_EuclidSPAgg_Q
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Corollary 8.3** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.34 (PDF p.36)). Let `n ≥ 3`, and let `f ∈ A_{n,d}` satisfy
`AR(f) < n − 1`. Then there are an orthonormal frame `B` and fixed ranks `k_j ∈ {2, …, n − 1}` such
that `AR(Q_{B,k}) ≤ AR(f)`. The rule `Q_{B,k}` can be chosen as the normalized representative
from Theorem 8.1.

**Formalization Note** Ranks are 0-based: `k_j ∈ {2, …, n − 1}` is `1 ≤ k j ∧ k j + 2 ≤ n`.
The second sentence is the conjunct `InF (Q B k) ∧ IsNormalized (Q B k)`: together with
`AR (Q B k) ≤ AR f` it says `Q B k` is a normalized member of `F_{n,d}` with ratio at most
`AR f`, which is what Theorem 8.1 supplies. `n − 1` is the natural number `n − 1` (`n ≥ 3`) cast to
`ℝ≥0∞`. `d ≥ 1` is standing (p.8). -/
theorem corollary_8_3 (n d : ℕ) (hn : 3 ≤ n) (hd : 1 ≤ d) (f : Mech n d) (hf : InA f)
    (hAR : AR f < ((n - 1 : ℕ) : ENNReal)) :
    ∃ (B : OrthonormalBasis (Fin d) ℝ (E d)) (k : Fin d → Fin n),
      (∀ j, 1 ≤ (k j : ℕ) ∧ (k j : ℕ) + 2 ≤ n) ∧ AR (Q B k) ≤ AR f ∧
        InF (Q B k) ∧ IsNormalized (Q B k) := by sorry

end EuclidSPAgg
