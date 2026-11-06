-- Prove2me | Theorems.Thm_FewExperts_proposition_2_harvest_gain
-- name    : FewExperts.proposition_2_harvest_gain
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:21.129665+00:00
-- url     : https://prove2.me/theorems/4a5b1d9f-4c5d-47f5-9c6d-33f7bfb4b06b
-- title:
--   Proposition 2 — HarvestGain: lead $\le2r(\ell+1)$, failure probability $\le\log\widetilde T/32r$, loss $\le16\sqrt{\widetilde T}$, $\le\log\widetilde T$ subscriptions
-- statement:
--   For all sufficiently large $N$ and $T$, take a parameter $\ell>0$ with $\alpha\ell\ge1$, a horizon $1\le\widetilde T\le T$, a baseline $\mathcal B$ predicting mixtures, and gains in $[0,1]$. The run $\mathcal A=$ HarvestGain$(\ell,\widetilde T,\mathcal B)$ has the following properties.
--
--   1. **(i)** For every choice of thresholds, every expert $i$ and every round $t$ up to and including the stopping round (up to $\widetilde T$ if the run does not stop),
--   $$
--   G_t^i-G_t^{\mathcal A}\le 2r(\ell+1). \tag{5}
--   $$
--   2. **(ii)** Over the random thresholds, the probability that $\mathcal A$ fails is at most $(\log\widetilde T)/32r$. Here $\mathcal A$ fails if it stops at a round $t$ with
--   $$
--   G_t^{\mathcal A}<G_t^{\mathcal B}+\alpha\ell-16\sqrt{\widetilde T}. \tag{6}
--   $$
--   3. **(iii)** For every choice of thresholds, during the whole run,
--   $$
--   G_t^{\mathcal A}\ge G_t^{\mathcal B}-16\sqrt{\widetilde T}. \tag{7}
--   $$
--   4. **(iv)** For every choice of thresholds, $\mathcal A$ subscribes to at most $\log\widetilde T$ experts (its transition experts at all recursion depths). Every expert in $\mathcal A$'s prediction at a round is either in $\mathcal B$'s prediction at that round or one of these.
--
--   This proposition is the engine of the main algorithm. Each epoch either gains about $\alpha\ell$ over the sampled baseline or loses little.
--
--   Differences from the source:
--   - reading: there is an algorithm 𝒜 → the algorithm of the proof, HarvestGain of Algorithm 3 (harvest); reason: the explicit algorithm implies the existence statement
--   - encoding: a baseline algorithm ℬ (randomness fixed, p.17) → the sequence b of ℬ's mixed predictions on the fixed gain sequence (probability vectors on rounds 1, …, T̃); reason: for fixed gains and fixed randomness a baseline is determined by its predictions; every realization is covered
--   - encoding: floors and ceilings omitted (p.13): 1/α levels, m = 4r/q, 2r scales, 2⁹rs/α epochs → K = ⌊1/α⌋ levels (exponent 1/α − j read as K − j), m = ⌈4r/q⌉, ⌈2r⌉ scales, ⌈2⁹rs/α⌉ epochs per scale; reason: the paper omits them where they do not materially affect the analysis; the floor keeps the top threshold Kαℓ ≤ ℓ, which Proposition 2 (i) uses
--   - encoding: B′ = two-expert Hedge "by Lemma 2" (rate left implicit); ties to "the first expert" → B′ = Hedge with rate √(ln 2/T̃′) on the streams of B and i*; ties broken towards the lowest index of Fin N; reason: the rate of Lemma 2's Hedge with n = 2 and horizon T̃′; "first" read as lowest index
--   - encoding: T and N sufficiently large (convention of §3, p.13, for everything outside §3) → ∃ N₀ T₀, ∀ N ≥ N₀, ∀ T ≥ T₀; reason: the paper's own convention made explicit
--   - generalization: (iv) at most log T̃ experts other than those used by ℬ → all experts 𝒜 subscribes to (its transition experts) number at most log T̃, and every expert in 𝒜's prediction is in ℬ's prediction at that round or among them; reason: counting also experts that ℬ uses only strengthens the bound; it implies the printed clause
--   - encoding: the probability in (ii) → the outer measure under thrTapeLaw (independent uniform thresholds for every expert and recursion depth) of the failure event is ≤ (log T̃)/32r; reason: the threshold device has the law (8); fresh thresholds at every depth, as in Algorithm 3
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), Proposition 2, pp.15–16 (PDF pp.16–17), with Algorithm 3, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_FewExperts_harvest

namespace FewExperts

open MeasureTheory

/-- **Proposition 2 (HarvestGain).**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Proposition 2, pp.15–16 (PDF 16–17), with the algorithm `A` of its proof
(Algorithm 3, p.16).

For `N`, `T` large enough, every `ℓ > 0` with `αℓ ≥ 1`, every horizon `1 ≤ T̃ ≤ T`, every
baseline `B` whose predictions `b u` (`u = 1, …, T̃`) are mixtures, and every gain sequence `h`
with values in `[0, 1]`, the run `A = HarvestGain(ℓ, T̃, B)` (`harvest N T ℓ T̃ b h τ`, threshold
tape `τ`) satisfies:

1. (i), (5): for every tape, every expert `i` and every round `t` up to and including the
   stopping round (or up to `T̃` if `A` does not stop), `G_t^i − G_t^A ≤ 2r(ℓ + 1)`;
2. (ii): the probability over the threshold tape that `A` fails — it stops, and at that round
   `G_t^A < G_t^B + αℓ − 16√T̃` (6) — is at most `(log T̃)/(32r)`;
3. (iii), (7): for every tape, `G_t^A ≥ G_t^B − 16√T̃` during the whole run;
4. (iv): for every tape, `A` subscribes to at most `log T̃` experts (the transition experts of
   all recursion depths), and every expert in `A`'s predictions is used by `B` at that round or
   is one of them.

**Formalization Note** Logs are base 2 (`lg`), `r = log T`. "Sufficiently large" (p.13) is
`∃ N₀ T₀`. The probability in (ii) is over the threshold tape (`thrTapeLaw`), for fixed gains and
baseline, and is stated as an upper bound on the outer measure of the failure event. -/
theorem proposition_2_harvest_gain :
    ∃ N₀ T₀ : ℕ, ∀ N T : ℕ, N₀ ≤ N → T₀ ≤ T →
    ∀ ℓ : ℝ, 0 < ℓ → 1 ≤ alpha N T * ℓ →
    ∀ Ttil : ℕ, 1 ≤ Ttil → Ttil ≤ T →
    ∀ b h : ℕ → Fin N → ℝ, (∀ u, 1 ≤ u → u ≤ Ttil → IsProbVec (b u)) → IsGainSeq Ttil h →
      (∀ τ : ThrTape N, ∀ i t, t ≤ (harvest N T ℓ Ttil b h τ).stopOrEnd Ttil →
          cumGain h t i - cumMix h (harvest N T ℓ Ttil b h τ).pred t ≤ 2 * rT T * (ℓ + 1)) ∧
      thrTapeLaw N {τ | (harvest N T ℓ Ttil b h τ).Fails (alpha N T) ℓ Ttil b h} ≤
          ENNReal.ofReal (lg Ttil / (32 * rT T)) ∧
      (∀ τ : ThrTape N, ∀ t, t ≤ (harvest N T ℓ Ttil b h τ).stopOrEnd Ttil →
          cumMix h b t - 16 * Real.sqrt Ttil ≤ cumMix h (harvest N T ℓ Ttil b h τ).pred t) ∧
      (∀ τ : ThrTape N, ((harvest N T ℓ Ttil b h τ).subs.card : ℝ) ≤ lg Ttil ∧
          ∀ u, 1 ≤ u → u ≤ (harvest N T ℓ Ttil b h τ).stopOrEnd Ttil → ∀ i,
            (harvest N T ℓ Ttil b h τ).pred u i ≠ 0 → b u i ≠ 0 ∨ i ∈ (harvest N T ℓ Ttil b h τ).subs) := by sorry

end FewExperts
