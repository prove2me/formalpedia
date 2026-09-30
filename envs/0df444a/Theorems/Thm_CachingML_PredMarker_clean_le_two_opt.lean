-- Prove2me | Theorems.Thm_CachingML_PredMarker_clean_le_two_opt
-- name    : CachingML.PredMarker.clean_le_two_opt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T16:04:18.769572+00:00
-- url     : https://prove2.me/theorems/7cfa0553-a7de-44cc-8f5b-3caf09ccbc4e
-- title:
--   Claim 1 — the optimal algorithm suffers at least $Q/2$ cache misses
-- statement:
--   Let $k \ge 1$ be the cache size, $\sigma$ a request sequence, $Q(\sigma)$ the number of clean elements of its Marker phases, and $\mathrm{Opt}(\sigma)$ the least number of misses of any eviction schedule starting from the empty cache. Then
--
--   $$Q(\sigma) \le 2\,\mathrm{Opt}(\sigma).$$
--
--   This is the classical lower bound on the offline optimum of Fiat, Karp, Luby, McGeoch, Sleator and Young (1991), which the paper cites as Claim 1 without proof. It is the lower bound against which every chain-based upper bound on Predictive Marker is compared in the proof of Theorem 3.3.
--
--   **Formalization Note** The statement is written in the integer form $Q \le 2\,\mathrm{Opt}$ of "$\mathrm{Opt} \ge Q/2$".
-- source:
--   Lykouris, Vassilvitskii, Competitive Caching with Machine Learned Advice, arXiv:1802.05399v4, p. 12, Claim 1 (citing Fiat et al. [FKL+91])

import Mathlib
import Definitions.Def_CachingML_PredMarker_opt
import Definitions.Def_CachingML_PredMarker_cleanCount

namespace CachingML.PredMarker

/-- Claim 1 of Lykouris–Vassilvitskii (arXiv:1802.05399v4, p. 12), citing Fiat et al. [FKL+91]: the
offline optimum suffers at least `Q/2` cache misses, `Q` being the number of clean elements. -/
theorem clean_le_two_opt {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (σ : List α) :
    cleanCount k σ ≤ 2 * opt k σ := by sorry

end CachingML.PredMarker
