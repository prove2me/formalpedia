-- Prove2me | Theorems.Thm_FewExperts_theorem_4_polylog_subscriptions
-- name    : FewExperts.theorem_4_polylog_subscriptions
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:55:42.104149+00:00
-- url     : https://prove2.me/theorems/0a202b0b-9c14-40a0-9d13-8884a475e1f4
-- title:
--   Theorem 4 — regret $O(\sqrt T\log^2T\log N(\log N+\log\log T)\sqrt{\log\log T+\log\log N})$ w.p. $1-\frac1T$ with $O(\log^6T\log N(\log N+\log\log T)^2)$ experts
-- statement:
--   Consider prediction with expert advice against an oblivious adversary: $N$ experts, $T$ rounds, and gains $g_t^i\in[0,1]$ fixed in advance. Logarithms are base 2.
--
--   There are a constant $C>0$ and thresholds $N_0,T_0$ with the following property. For all $N\ge N_0$, $T\ge T_0$ and every gain array, the algorithm of Algorithms 3–4, which plays experts sampled from its mixed predictions, satisfies:
--
--   1. with probability at least $1-1/T$ over its randomness, its regret against the best expert is at most
--   $$
--   C\,\sqrt T\,\log^2T\,\log N\,(\log N+\log\log T)\,\sqrt{\log\log T+\log\log N};
--   $$
--   2. on every execution, every expert it plays in rounds $1,\dots,T$ is one it has subscribed to, and it subscribes to at most
--   $$
--   C\,\log^6T\,\log N\,(\log N+\log\log T)^2
--   $$
--   distinct experts (the sampled experts of every epoch, the transition experts of every HarvestGain run, and the fallback expert).
--
--   In words, polylogarithmically many experts suffice for $\widetilde O(\sqrt T)$ regret, whereas limited-switching algorithms need $\widetilde\Theta(\sqrt T)$ of them.
--
--   Differences from the source:
--   - reading: there is an efficient algorithm → the explicit algorithm fewExpertsAlg of Algorithms 3–4 with sampled play; no running-time clause; reason: the paper defines no efficiency notion and states no time bound for Theorem 4; the explicit algorithm implies the existence statement and its polynomial per-round work can be read off the definition
--   - encoding: O(·) and "T and N sufficiently large" (p.13) → ∃ C > 0, ∃ N₀ T₀, ∀ N ≥ N₀, ∀ T ≥ T₀; reason: the paper's own conventions made explicit
--   - encoding: floors and ceilings omitted (p.13): 1/α levels, m = 4r/q, 2r scales, 2⁹rs/α epochs → K = ⌊1/α⌋ levels (exponent 1/α − j read as K − j), m = ⌈4r/q⌉, ⌈2r⌉ scales, ⌈2⁹rs/α⌉ epochs per scale; reason: the paper omits them where they do not materially affect the analysis; the floor keeps the top threshold Kαℓ ≤ ℓ, which Proposition 2 (i) uses
--   - encoding: B′ = two-expert Hedge "by Lemma 2" (rate left implicit); ties to "the first expert" → B′ = Hedge with rate √(ln 2/T̃′) on the streams of B and i*; ties broken towards the lowest index of Fin N; reason: the rate of Lemma 2's Hedge with n = 2 and horizon T̃′; "first" read as lowest index
--   - encoding: the algorithm's randomness and the sampled choice i*_t → independent uniform variables per label (thresholds and samples of each epoch, one per round for the play); the played expert is drawn from the mixture by the inverse-CDF device sampleFin; reason: §3.1: the algorithm samples from its mix; the device draws expert i with probability equal to its weight
--   - encoding: the fallback "Follow an already subscribed expert" (Algorithm 4, line 21) → the first sampled expert of the first epoch; reason: any subscribed expert is allowed; this one is always subscribed
--   - generalization: the number of distinct experts which are ever used (the experts subscribed to: p.1, "its cost is the total number of subscriptions") → every expert played in rounds 1, …, T lies in subscribedSet, and the card of subscribedSet is bounded; subscribedSet = the sampled multiset of every epoch that runs, every transition expert of every recursion depth of its HarvestGain run (HGRun.subs), and the fallback expert; reason: subscribedSet contains every expert the algorithm actually subscribes to (HGRun.subs may also count a transition of a recursive run after the outer run stopped), so bounding its card implies the paper's bound on subscriptions, and played ⊆ subscribed gives the bound on played experts
--   - encoding: Pr[bad event] ≤ β → the (outer) measure of the bad event is ≤ ENNReal.ofReal β; reason: equal for measurable events; no measurability statement is needed
--   - encoding: experts 1, …, N; rounds 1, …, T → experts Fin N with N ≠ 0 (instance argument); rounds 1-based; the gain array is a function on ℕ constrained on 1, …, T; reason: Lean convention; N ≥ N₀ ≥ 1 makes N ≠ 0 automatic
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), Theorem 4, p.15 (PDF p.16); algorithm: Algorithms 3–4, pp.16, 20 (PDF pp.17, 21); sampling: §3.1, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_FewExperts_fewExpertsAlg

namespace FewExperts

open MeasureTheory

/-- **Theorem 4: Õ(√T) regret with polylogarithmically many experts.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Theorem 4, p.15 (PDF 16): "For the problem of oblivious-adversary predictions with
expert advice, there is an efficient algorithm which achieves (with probability at least
1 − 1/T) regret O(√T log²T log N (log N + log log T) √(log log T + log log N)), and the number of
distinct experts which are ever used is at most O(log⁶T log N (log N + log log T)²) on every
execution."

There are a constant `C > 0` and thresholds `N₀`, `T₀` such that for all `N ≥ N₀`, `T ≥ T₀` and
every gain array `g ∈ [0, 1]^{T × N}` fixed in advance (oblivious adversary), the algorithm
`fewExpertsAlg N T` of Algorithms 3–4 (with predictions sampled from its mixtures) satisfies:

1. with probability at least `1 − 1/T` over its randomness, its regret against the best expert
   is at most `C √T log²T log N (log N + log log T) √(log log T + log log N)`;
2. for every value of its randomness, every expert it plays in rounds `1, …, T` is one it
   subscribed to (`subscribedSet`), and it subscribes to at most
   `C log⁶T log N (log N + log log T)²` distinct experts.

**Formalization Note** Logs are base 2. The algorithm depends only on `(N, T)`; it sees at round
`t` only its randomness and the gains of rounds `< t`, and `g` is quantified before its
randomness. "Distinct experts ever used" is the set of experts subscribed to (p.1: "its cost is
the total number of subscriptions"); `subscribedSet` contains the actual subscriptions and every
played expert. The `O(·)` and "T and N sufficiently large" (p.13) are `∃ C, N₀, T₀`. The
probability bound is an upper bound on the outer measure of the bad event. -/
theorem theorem_4_polylog_subscriptions :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ T₀ : ℕ, ∀ N T : ℕ, N₀ ≤ N → T₀ ≤ T → ∀ [NeZero N],
      ∀ g : ℕ → Fin N → ℝ, IsGainSeq T g →
        fewExpertsLaw {ω | C * regretRate N T < gainRegret T g (fewExpertsPlay N T ω g)} ≤
            ENNReal.ofReal (1 / T) ∧
        ∀ ω : Rand, (Finset.Icc 1 T).image (fewExpertsPlay N T ω g) ⊆ subscribedSet N T ω g ∧
          ((subscribedSet N T ω g).card : ℝ) ≤ C * subsRate N T := by sorry

end FewExperts
