-- Prove2me | Theorems.Thm_CausalFailureRank_infinite_rank
-- name    : CausalFailureRank.infinite_rank
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:54.255217+00:00
-- url     : https://prove2.me/theorems/ad48ff20-f50a-49b6-8cbd-971135595de9
-- title:
--   Theorem 3.1, infinite-rank clause — zero observations and bounded bill
-- statement:
--   If the initial rank is infinite then, under any quotas and any call limit $H\ge H_0+\min(N,q)$, a deterministic immediate-execution policy succeeds on every sample with no observation at all, and its actual correction bill is at most $\min(N,q)f_{\max}$. So its failure probability is $0$.
--
--   Differences from the source:
--   - generalization: limits satisfying App. B.5 → $H\ge H_0+\min(N,q)$ and any quotas; reason: implied by (25); the infinite-rank policy buys no reviews
--   - generalization: "the actual correction bill remains bounded" → success on every sample and an actual correction bill at most $\min(N,q)f_{\max}$ on every sample; reason: B.4 rule 1 and §2 ("Every policy uses at most min(N, q) genuine corrections") give it; the explicit bound implies the source’s boundedness, and sure success gives failure probability $0$
--   - encoding: stages $1,\dots,N+1$ → 0-based stages, terminal $i\ge N$; reason: Lean indexing; no instance changes
--   - generalization: rational probabilities, fees and risk parameters → real ones; reason: rationality serves only computability, which is not claimed here; the rational case is an instance
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), Theorem 3.1, p.6; App. B.4, rule 1, p.17

import Mathlib
import Definitions.Def_CausalFailureRank_coefficient
import Definitions.Def_CausalFailureRank_step

open Filter Topology MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

/-- **The infinite-rank clause.** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), Theorem 3.1, p.6: "If the initial rank is infinite, zero
observations suffice and the actual correction bill remains bounded." with App. B.4, rule 1, p.17: "If
ρ = ∞, take no observations, write blindly, and after each actual reported error choose an
infinite-rank child and execute its real compatible correction."

**Formalization Note.** A deterministic immediate-execution policy, on every sample: zero reviews,
success (so failure probability `0`, and it is δ-safe for every `δ ≥ 0`), bill at most
`min(N, q) f_max`. The call cap needs only `H ≥ H₀ + min(N, q)`, implied by (25); any quotas. -/
theorem infinite_rank (I : Instance N q) (hrank : rank I 0 Finset.univ = ⊤) (caps : Caps N)
    (hH : ((∑ i, I.normalCalls i + min N q : ℕ) : ℕ∞) ≤ caps.H) :
    ∃ π : History I → Action N q, ∀ ω,
      (∀ n, (runFrom I .currentPay caps π (initState I) ω n).history.countP Event.isObs = 0) ∧
      SuccessFrom I .currentPay caps π (initState I) ω ∧
      billFrom I .currentPay caps π (initState I) ω ≤ ENNReal.ofReal ((min N q : ℕ) * fmax I) := by sorry

end CausalFailureRank
