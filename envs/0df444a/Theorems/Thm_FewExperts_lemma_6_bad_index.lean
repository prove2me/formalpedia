-- Prove2me | Theorems.Thm_FewExperts_lemma_6_bad_index
-- name    : FewExperts.lemma_6_bad_index
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:03.53808+00:00
-- url     : https://prove2.me/theorems/bd517c36-538e-44c4-a351-a0d7043d0d94
-- title:
--   Lemma 6 — $\Pr[\text{transition at a bad index of }i]\le p^{1/\alpha-1}+2(1-p)\Pr[\text{transition with }i]$
-- statement:
--   Fix a run of HarvestGain$(\ell,\widetilde T,\mathcal B)$ with $\ell>0$, $\alpha\ell\ge1$, $1\le\widetilde T\le T$, a baseline $\mathcal B$ predicting mixtures, and gains in $[0,1]$. The gains and $\mathcal B$ are fixed, and the run's thresholds $r_i$ are random. For every expert $i$,
--
--   $$
--   \Pr[\mathcal A\text{ transitions with a bad index of }i]\le p^{K-1}+2(1-p)\cdot\Pr[\mathcal A\text{ transitions with }i],
--   $$
--
--   where "transitions with $i$" means $i^*=i$, and the index $r_i$ is bad for $i$ when $t_{r_i}<\infty$ and $t_{r_i+1}>t_{r_i}+\widetilde T/2$.
--
--   Summed over the experts, this bounds the probability of a bad transition by $Np^{K-1}+2(1-p)$, which is (12).
--
--   Differences from the source:
--   - encoding: floors and ceilings omitted (p.13): 1/α levels, m = 4r/q, 2r scales, 2⁹rs/α epochs → K = ⌊1/α⌋ levels (exponent 1/α − j read as K − j), m = ⌈4r/q⌉, ⌈2r⌉ scales, ⌈2⁹rs/α⌉ epochs per scale; reason: the paper omits them where they do not materially affect the analysis; the floor keeps the top threshold Kαℓ ≤ ℓ, which Proposition 2 (i) uses
--   - encoding: Pr over the run's thresholds, everything else fixed → levelLaw N: one independent uniform per expert, mapped to r_i by the threshold device; reason: the device has exactly the law (8)
--   - encoding: a baseline algorithm ℬ (randomness fixed, p.17) → the sequence b of ℬ's mixed predictions on the fixed gain sequence (probability vectors on rounds 1, …, T̃); reason: for fixed gains and fixed randomness a baseline is determined by its predictions; every realization is covered
--   - encoding: Pr[bad event] ≤ β → the (outer) measure of the bad event is ≤ ENNReal.ofReal β; reason: equal for measurable events; no measurability statement is needed
--   - generalization: T and N sufficiently large (convention of §4) → all N, T; reason: the proof of this lemma uses no largeness; the statement specializes to large N, T
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), Lemma 6, p.17 (PDF p.18), and the definitions of t_j and bad indices on the same page

import Mathlib
import Definitions.Def_FewExperts_harvest

namespace FewExperts

open MeasureTheory

/-- **Lemma 6 (bad thresholds are rarely the winning bet).**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Lemma 6, p.17 (PDF 18), in the setting of the proof of Proposition 2 (ii): "Fix the
gain sequence and the entire random tape of B. … We have, for each expert i,
Pr[A transitions with bad index of i] ≤ p^{1/α−1} + 2(1 − p) · Pr[A transitions with i]."

Under the hypotheses of Proposition 2, for every expert `i`, over the run's own thresholds
(`levelLaw N`: one independent uniform variable per expert, mapped to the index `r_i`), the
probability that `A` transitions with expert `i` at an index `r_i` that is bad for `i`
(`IsBadIndex`) is at most `p^{K−1} + 2(1 − p) · Pr[A transitions with i]`.

**Formalization Note** `K = ⌊1/α⌋` is the number of threshold levels (`numLevels`), which the
paper writes `1/α` (floors omitted, p.13); the exponent `1/α − 1` is `K − 1`. -/
theorem lemma_6_bad_index (N T : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) (hαℓ : 1 ≤ alpha N T * ℓ) (Ttil : ℕ)
    (hT1 : 1 ≤ Ttil) (hTT : Ttil ≤ T) (b h : ℕ → Fin N → ℝ)
    (hb : ∀ u, 1 ≤ u → u ≤ Ttil → IsProbVec (b u)) (hh : IsGainSeq Ttil h) (i : Fin N) :
    levelLaw N {u | ∃ t r, transOf N T ℓ Ttil b h u = some (t, i, r) ∧
        IsBadIndex N T ℓ Ttil b h i r} ≤
      ENNReal.ofReal (pT T ^ (numLevels N T - 1)) +
        ENNReal.ofReal (2 * (1 - pT T)) *
          levelLaw N {u | ∃ t r, transOf N T ℓ Ttil b h u = some (t, i, r)} := by sorry

end FewExperts
