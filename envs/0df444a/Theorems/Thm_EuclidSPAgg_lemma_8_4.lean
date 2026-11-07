-- Prove2me | Theorems.Thm_EuclidSPAgg_lemma_8_4
-- name    : EuclidSPAgg.lemma_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:44.201342+00:00
-- url     : https://prove2.me/theorems/7b166985-d035-4ade-955c-c100ef10042d
-- title:
--   Lemma 8.4 — every fixed-frame order-statistic rule has ratio at least $R_{n,d}$
-- statement:
--   For every $n\ge2$, every orthonormal frame $\mathcal B$ of $\mathbb R^d$ and every rank vector $k\in[n]^d$,
--   $$
--   \mathrm{AR}(Q_{\mathcal B,k})\ge R_{n,d}=\mathrm{AR}(\mathrm{CM}_{n,d}).
--   $$
--
--   Among fixed-frame order-statistic rules the coordinate-wise median has the least ratio.
--
--   **Formalization Note** Ranks are $0$-based, so every rank vector in $[n]^d$ is representable.
--
--   Differences from the source:
--   - encoding: k ∈ [n]^d → k : Fin d → Fin n; reason: 0-based ranks; the same set of rank vectors
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Lemma 8.4, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_EuclidSPAgg_Q
import Definitions.Def_EuclidSPAgg_medianRatio
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Lemma 8.4** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.34 (PDF p.36)). For every `n ≥ 2` and every fixed-frame order-statistic
rule `Q_{B,k}`, `AR(Q_{B,k}) ≥ R_{n,d}`.

**Formalization Note** `B` is any orthonormal basis of `E` and `k` any rank vector in `[n]^d`
(0-based, `k : Fin d → Fin n`). `R_{n,d} = AR(CM_{n,d})` is `medianRatio n d`. `d ≥ 1` is
standing (p.8). -/
theorem lemma_8_4 (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) (B : OrthonormalBasis (Fin d) ℝ (E d))
    (k : Fin d → Fin n) :
    medianRatio n d ≤ AR (Q B k) := by sorry

end EuclidSPAgg
