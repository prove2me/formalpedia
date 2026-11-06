-- Prove2me | Theorems.Thm_FewExperts_sec4_2_sampling_bound
-- name    : FewExperts.sec4_2_sampling_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:55:05.45521+00:00
-- url     : https://prove2.me/theorems/a278f04a-e093-475d-af54-bd034bc618b0
-- title:
--   §4.2, p.20 — $\Pr[\max_{j\in I}G^j<u_t]\le(1-q)^m\le e^{-mq}\le\frac1{4T^3}$, and the best sample is beaten by at most $q$ mass w.p. $1-\frac1{4T}$
-- statement:
--   Let $q=\alpha/(2^{10}r)$ and $m=\lceil4r/q\rceil$. For all sufficiently large $N$ and $T$:
--
--   1. Let $\mathcal D$ be a probability vector on the experts, $x$ a score on the experts, and $u$ a threshold with $\mathcal D\{x>u\}\le q\le\mathcal D\{x\ge u\}$. If $I=(i_1,\dots,i_m)$ are $m$ independent draws from $\mathcal D$, then
--   $$
--   \Pr\bigl[\max_{j}x_{i_j}<u\bigr]\le(1-q)^m\le e^{-mq}\le\frac{1}{4T^3}.
--   $$
--   2. For every gain array, consider every epoch of the algorithm that runs, starting after round $t_0$, and every $t\in(t_0,T]$. With probability at least $1-1/(4T)$, at all of these, the experts whose interval gain $G^i_{(t_0,t]}$ exceeds that of every sampled expert have total $\mathcal D$-mass at most $q$.
--
--   This event, assumed in the rest of the analysis, gives (16) for all but a $q$-fraction of the experts.
--
--   Differences from the source:
--   - encoding: floors and ceilings omitted (p.13): 1/α levels, m = 4r/q, 2r scales, 2⁹rs/α epochs → K = ⌊1/α⌋ levels (exponent 1/α − j read as K − j), m = ⌈4r/q⌉, ⌈2r⌉ scales, ⌈2⁹rs/α⌉ epochs per scale; reason: the paper omits them where they do not materially affect the analysis; the floor keeps the top threshold Kαℓ ≤ ℓ, which Proposition 2 (i) uses
--   - encoding: T and N sufficiently large (convention of §3, p.13, for everything outside §3) → ∃ N₀ T₀, ∀ N ≥ N₀, ∀ T ≥ T₀; reason: the paper's own convention made explicit
--   - encoding: I = m independent samples from 𝒟 → m independent uniforms pushed through the inverse-CDF device sampleFin; reason: the device draws expert i with probability 𝒟(i)
--   - reading: a union bound over all times and over all samplings … always → every epoch that runs (t₀ < T) and every t ∈ (t₀, T]; reason: these are the times and samplings at which the event is used
--   - encoding: Pr[bad event] ≤ β → the (outer) measure of the bad event is ≤ ENNReal.ofReal β; reason: equal for measurable events; no measurability statement is needed
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §4.2, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_FewExperts_fewExpertsAlg

namespace FewExperts

open MeasureTheory

/-- **§4.2 sampling bound: `m` samples from `𝒟` miss at most `q` of its mass.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), §4.2, p.20 (PDF 21): "For a fixed time t, choose u_t such that
Pr_{i∼𝒟}[G^i_{(t0,t]} > u_t] ≤ q and Pr_{i∼𝒟}[G^i_{(t0,t]} ≥ u_t] ≥ q. Then
Pr[max_{j∈I} G^j_{(t0,t]} < u_t] ≤ (1 − q)^m ≤ e^{−mq} ≤ 1/(4T³), where the probability is over
the random choice of I. By a union bound over all times and over all samplings, with probability
at least 1 − 1/4T, the best expert in I is always beaten by at most q mass of experts (where mass
is measured under 𝒟)."

For `N`, `T` large enough, with `q = α/(2¹⁰r)` and `m = ⌈4r/q⌉`:

1. for every probability vector `𝒟`, every score `x : [N] → ℝ` and every `u` with
   `𝒟{x > u} ≤ q ≤ 𝒟{x ≥ u}`, if `I = (i₁, …, i_m)` are `m` independent draws from `𝒟`, then
   `Pr[max_j x_{i_j} < u] ≤ (1 − q)^m`;
2. `(1 − q)^m ≤ e^{−mq}` and `e^{−mq} ≤ 1/(4T³)`;
3. for every gain array, the probability (over the algorithm's randomness) that in some epoch
   that runs, at some time `t` after its start `t0`, more than `q` of `𝒟`'s mass beats every
   sampled expert on the interval gains `G^i_{(t0,t]}` (the complement of `SampOK`) is at most
   `1/(4T)`.

**Formalization Note** A draw from `𝒟` is `sampleFin 𝒟 v` with `v` uniform on `[0, 1]` (the
algorithm's sampling device), so `I` has the law of `m` independent uniform variables pushed
through it. "Sufficiently large" (p.13) is `∃ N₀ T₀`. Probabilities are upper bounds on outer
measures. -/
theorem sec4_2_sampling_bound :
    ∃ N₀ T₀ : ℕ, ∀ N T : ℕ, N₀ ≤ N → T₀ ≤ T → ∀ [NeZero N],
      (∀ (D x : Fin N → ℝ) (u0 : ℝ), IsProbVec D →
          ∑ i ∈ Finset.univ.filter (fun i => u0 < x i), D i ≤ qParam N T →
          qParam N T ≤ ∑ i ∈ Finset.univ.filter (fun i => u0 ≤ x i), D i →
          Measure.pi (fun _ : Fin (mParam N T) => (volume : Measure unitInterval))
              {v | ∀ j, x (sampleFin D (v j)) < u0} ≤
            ENNReal.ofReal ((1 - qParam N T) ^ mParam N T)) ∧
      (1 - qParam N T) ^ mParam N T ≤ Real.exp (-(mParam N T * qParam N T)) ∧
      Real.exp (-(mParam N T * qParam N T)) ≤ 1 / (4 * (T : ℝ) ^ 3) ∧
      (∀ g : ℕ → Fin N → ℝ, IsGainSeq T g →
        fewExpertsLaw {ω | ¬ SampOK N T ω g} ≤ ENNReal.ofReal (1 / (4 * T))) := by sorry

end FewExperts
