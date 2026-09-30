-- Prove2me | Theorems.Thm_CachingML_PredMarker_opt_le_cleanCount
-- name    : CachingML.PredMarker.opt_le_cleanCount
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T16:07:30.800984+00:00
-- url     : https://prove2.me/theorems/2f729b2c-8041-41c2-a155-a3339b4d6017
-- title:
--   Proof of Theorem 3.3 — $\mathrm{Opt}(\sigma) \le Q$
-- statement:
--   Let $k \ge 1$ be the cache size, $\sigma$ a request sequence, $Q(\sigma)$ the number of clean elements of its Marker phases, and $\mathrm{Opt}(\sigma)$ the least number of misses of any eviction schedule starting from the empty cache. Then
--
--   $$\mathrm{Opt}(\sigma) \le Q(\sigma).$$
--
--   The paper uses this inequality, without a separate statement, in the last sentence of the proof of Theorem 3.3, to pass from the accuracy condition $\eta \le \epsilon\,\mathrm{Opt}(\sigma)$ to the per-chain average $\eta / Q \le \epsilon$. Together with Claim 1 it pins $\mathrm{Opt}(\sigma)$ between $Q/2$ and $Q$.
-- source:
--   Lykouris, Vassilvitskii, Competitive Caching with Machine Learned Advice, arXiv:1802.05399v4, p. 16, proof of Theorem 3.3, last sentence ("since Opt(σ) ≤ Q")

import Mathlib
import Definitions.Def_CachingML_PredMarker_opt
import Definitions.Def_CachingML_PredMarker_cleanCount

namespace CachingML.PredMarker

/-- The step `Opt(σ) ≤ Q` of the proof of Theorem 3.3 (Lykouris–Vassilvitskii, arXiv:1802.05399v4,
p. 16, last sentence of the proof): the offline optimum suffers at most as many cache misses as there
are clean elements. -/
theorem opt_le_cleanCount {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (σ : List α) :
    opt k σ ≤ cleanCount k σ := by sorry

end CachingML.PredMarker
