-- Prove2me | Theorems.Thm_FewExperts_sec4_2_subscription_count
-- name    : FewExperts.sec4_2_subscription_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:55:41.257117+00:00
-- url     : https://prove2.me/theorems/4076b0c5-84aa-4bb1-905d-1d943f2f3b81
-- title:
--   §4.2, p.22 — at most $2^{43}r^6s(s+\log r)^2$ distinct experts on every execution
-- statement:
--   For all sufficiently large $N$ and $T$, every gain array with values in $[0,1]$ and every value of the algorithm's randomness, every expert the algorithm of Theorem 4 plays in rounds $1,\dots,T$ is one it has subscribed to, and it subscribes to at most
--
--   $$
--   2^{43}\,r^6\,s\,(s+\log r)^2
--   $$
--
--   distinct experts, where $r=\log T$ and $s=\log N$. The subscriptions counted are the $m$ sampled experts of every epoch that runs, the transition experts of its HarvestGain run at every recursion depth, and the fallback expert.
--
--   This is the "every execution" clause of Theorem 4, with an explicit constant.
--
--   Differences from the source:
--   - generalization: the number of distinct experts which are ever used (the experts subscribed to: p.1, "its cost is the total number of subscriptions") → every expert played in rounds 1, …, T lies in subscribedSet, and the card of subscribedSet is bounded; subscribedSet = the sampled multiset of every epoch that runs, every transition expert of every recursion depth of its HarvestGain run (HGRun.subs), and the fallback expert; reason: subscribedSet contains every expert the algorithm actually subscribes to (HGRun.subs may also count a transition of a recursive run after the outer run stopped), so bounding its card implies the paper's bound on subscriptions, and played ⊆ subscribed gives the bound on played experts
--   - encoding: floors and ceilings omitted (p.13): 1/α levels, m = 4r/q, 2r scales, 2⁹rs/α epochs → K = ⌊1/α⌋ levels (exponent 1/α − j read as K − j), m = ⌈4r/q⌉, ⌈2r⌉ scales, ⌈2⁹rs/α⌉ epochs per scale; reason: the paper omits them where they do not materially affect the analysis; the floor keeps the top threshold Kαℓ ≤ ℓ, which Proposition 2 (i) uses
--   - encoding: T and N sufficiently large (convention of §3, p.13, for everything outside §3) → ∃ N₀ T₀, ∀ N ≥ N₀, ∀ T ≥ T₀; reason: the paper's own convention made explicit
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §4.2, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_FewExperts_fewExpertsAlg

namespace FewExperts

/-- **§4.2 subscription count: at most `2⁴³ r⁶ s(s + log r)²` experts on every execution.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), §4.2, p.22 (PDF 23): "Each run of BoostAdvantage subscribes to at most m sampled
experts, and the corresponding run of HarvestGain subscribes to at most log T additional experts.
Between each doubling of L, there are at most 2⁹rs/α runs of BoostAdvantage, and there are at
most 2r such doublings. Thus the total number of distinct experts which are ever used is at most
(2¹⁰r²s/α)(m + 2r) ≤ 2⁴³r⁶s(s + log r)²."

For `N`, `T` large enough, every gain array and every value of the algorithm's randomness, every
expert the algorithm of Theorem 4 plays in rounds `1, …, T` is one it subscribed to
(`subscribedSet`), and it subscribes to at most `2⁴³ r⁶ s (s + log r)²` distinct experts
(`r = log₂ T`, `s = log₂ N`).

**Formalization Note** "Experts ever used" is the set of experts subscribed to (the paper's cost,
p.1: "its cost is the total number of subscriptions"), which contains the experts played.
`subscribedSet` may count a few transition experts of recursive runs that never get subscribed,
so the bound is on a superset of the actual subscriptions. The algorithm carries the
ceilings `⌈2r⌉`, `⌈2⁹rs/α⌉`, `⌈4r/q⌉` that the paper omits; the displayed final bound is stated
as printed. "Sufficiently large" (p.13) is `∃ N₀ T₀`. -/
theorem sec4_2_subscription_count :
    ∃ N₀ T₀ : ℕ, ∀ N T : ℕ, N₀ ≤ N → T₀ ≤ T → ∀ [NeZero N],
      ∀ g : ℕ → Fin N → ℝ, IsGainSeq T g → ∀ ω : Rand,
        (Finset.Icc 1 T).image (fewExpertsPlay N T ω g) ⊆ subscribedSet N T ω g ∧
          ((subscribedSet N T ω g).card : ℝ) ≤ 2 ^ 43 * rT T ^ 6 * sN N * (sN N + lg (rT T)) ^ 2 := by sorry

end FewExperts
