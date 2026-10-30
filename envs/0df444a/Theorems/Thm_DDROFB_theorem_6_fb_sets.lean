-- Prove2me | Theorems.Thm_DDROFB_theorem_6_fb_sets
-- name    : DDROFB.theorem_6_fb_sets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:10:01.220531+00:00
-- url     : https://prove2.me/theorems/16d3b472-7010-4d5c-8d1e-4a8be346afd0
-- title:
--   Theorem 6: $\mathcal U^{FB}_\epsilon$ simultaneously imply a guarantee, with support function (24) (corrected: thresholds making $\mathcal P^{FB}$ a $1-\alpha$ confidence region, not bootstrapped)
-- statement:
--   Let $\mathbb P^*$ be a probability measure on $\mathbb R^d$ with independent components and bounded support, and let $\mathcal S = (\hat u^1,\dots,\hat u^N)$ be $N$ i.i.d. draws from $\mathbb P^*$, with law $\mathbb P^*_{\mathcal S}$ (the $N$-fold product). Let $\alpha \in \mathbb R$. To every sample $\mathcal S$ attach thresholds $m_b(\mathcal S) \le m_f(\mathcal S)$ and $\bar\sigma_f(\mathcal S), \bar\sigma_b(\mathcal S) > 0$ in $\mathbb R^d$, let $\mathcal P^{FB}(\mathcal S)$ be the forward–backward confidence region with these thresholds, and for $0<\epsilon<1$ let $\mathcal U^{FB}_\epsilon(\mathcal S)$ be the set (23):
--
--   $$
--   \mathcal U^{FB}_\epsilon = \Bigl\{ y_1 + y_2 - y_3 : y_2, y_3 \in \mathbb R^d_+,\ \sum_{i=1}^d \frac{y_{2i}^2}{2\bar\sigma_{fi}^2} + \frac{y_{3i}^2}{2\bar\sigma_{bi}^2} \le \log(1/\epsilon),\ m_{bi} \le y_{1i} \le m_{fi},\ i=1,\dots,d \Bigr\}.
--   $$
--
--   Assume that $\mathcal P^{FB}$ is a $1-\alpha$ confidence region: $\mathbb P^*_{\mathcal S}\bigl(\mathbb P^* \in \mathcal P^{FB}(\mathcal S)\bigr) \ge 1-\alpha$. Then:
--
--   1. With probability at least $1-\alpha$ with respect to the sample, the family $\{\mathcal U^{FB}_\epsilon(\mathcal S) : 0<\epsilon<1\}$ simultaneously implies a probabilistic guarantee for $\mathbb P^*$:
--   $$
--   \mathbb P^*_{\mathcal S}\Bigl(\text{for every } 0<\epsilon<1,\ \mathcal U^{FB}_\epsilon(\mathcal S) \text{ implies a probabilistic guarantee for } \mathbb P^* \text{ at level } \epsilon\Bigr) \;\ge\; 1-\alpha .
--   $$
--   2. For every sample $\mathcal S$, every $0<\epsilon<1$ and every $v \in \mathbb R^d$,
--   $$
--   \delta^*\bigl(v \mid \mathcal U^{FB}_\epsilon(\mathcal S)\bigr) = \sum_{i : v_i \ge 0} m_{fi} v_i + \sum_{i : v_i < 0} m_{bi} v_i + \sqrt{2\log(1/\epsilon)\Bigl(\sum_{i : v_i \ge 0} \bar\sigma_{fi}^2 v_i^2 + \sum_{i : v_i < 0} \bar\sigma_{bi}^2 v_i^2\Bigr)} .
--   $$
--
--   The theorem turns data on the means and forward/backward deviations of independent components into an explicit, second-order-cone-representable uncertainty set that protects every concave constraint at every level $\epsilon$ simultaneously, without knowing the mean or the support of $\mathbb P^*$.
--
--   Differences from the source:
--   - correction: thresholds t_i, σ̄_fi, σ̄_bi computed by the bootstrap of Algorithm 1 (p. 18; bootstrap tests are "only asymptotically valid", p. 8) → arbitrary thresholds mb S, mf S, σf S, σb S with the coverage hypothesis hcov: P∗_S(P∗ ∈ P^FB(S)) ≥ 1 − α; reason: with the bootstrapped thresholds the first clause is false: d = 1, P∗ = Uniform[−1, 1], N = 2, α = 0.1; for a sample {a, b} every bootstrap statistic takes only the values 0 and r = |b − a|/2, so t = σ̄_f = σ̄_b = r and U^FB_ϵ = [c − r − √(2 log(1/ϵ)) r, c + r + √(2 log(1/ϵ)) r] with c = (a + b)/2; whenever |a|, |b| < 0.18, at ϵ = 1/4 the right end hi of U^FB_ϵ is below 1/2, so the concave g(u) = u − hi is ≤ 0 on U^FB_ϵ while P∗(ũ ≤ hi) < 3/4, and the family fails for some ϵ with probability ≈ 0.58 > α; coverage at level 1 − α is the property the proof uses through Theorem 3
--   - generalization: m_bi = µ̂_i − t_i and m_fi = µ̂_i + t_i → arbitrary functions mb S ≤ mf S of the sample; reason: the proof uses only m_b ≤ m_f; µ̂ ∓ t with a threshold t ≥ 0 of the nonnegative statistic |µ̂_i − µ_0,i| is an instance
--   - generalization: 0 < α < 1 (the schema, p. 10) → any real α; reason: the statement for every α contains the paper's case
--   - reading: with probability 1 − α → with probability at least 1 − α; reason: Theorems 2 and 3, on which the proof rests, say "at least"
--   - reading: P^FB = {P : P_i ∈ P^FB_i, i = 1,…,d} (conditions on the marginals only) → PFB also requires independent components (HasIndepComponents P); reason: p. 9 defines the confidence region as the measures consistent with the a priori assumptions of the test, here independent components (Sec. 5.2, Theorem 6); the bound (22) applied in the proof holds only for independent marginals; P∗ is independent, so the coverage event is unchanged
--   - reading: P^FB_i ⊆ Θ(−∞,∞) under the section's standing assumption that P∗ has bounded support → PFB contains measures of unbounded support (bounded support is assumed of P∗ only, via hbdd); reason: Θ(−∞,∞) is the set of all Borel probability measures on ℝ (p. 9); since P∗ has bounded support the coverage event is the same under either reading
--   - encoding: for every x∗ and every f(u,x) concave in u (probabilistic guarantee, (2)) → every concave g : ℝ^d → ℝ (ImpliesGuarantee); reason: x∗ is fixed in (2), so only g = f(·,x∗) matters, and every concave g is f(·,x∗) for f(u,x) := g(u)
--   - encoding: thresholds σ̄_fi, σ̄_bi (divisors in (23)) and m_bi ≤ m_fi → hypotheses 0 < σf i, 0 < σb i and mb i ≤ mf i; reason: σ̄ = 0 divides by zero in (23), where Lean's y²/0 = 0 would silently drop the constraint; m_b > m_f makes (23) empty and (24) meaningless
--   - encoding: P∗ has bounded support → hbdd: ∃ R, ‖ũ‖ ≤ R P∗-almost surely; reason: the support is unknown, so the radius is existential
--   - encoding: probability with respect to the sampling → product measure Measure.pi of N copies of P∗ on samples S : Fin N → ℝ^d, applied to the event as an outer measure; reason: for a measurable event this is its probability; hypothesis and conclusion use the same notion
--   - encoding: δ∗(v| U^FB_ϵ) equal to the right-hand side of (24) → IsLUB of {⟪v, u⟫ : u ∈ UFB} at fbBound; reason: the least upper bound of the set is the supremum, without Lean's junk value for a real sSup
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 6, p. 19 (proof p. ec5 = PDF p. 43)

import Mathlib
import Definitions.Def_DDROFB_HasIndepComponents
import Definitions.Def_DDROFB_SimultaneouslyImplies
import Definitions.Def_DDROFB_PFB
import Definitions.Def_DDROFB_UFB
import Definitions.Def_DDROFB_fbBound
open MeasureTheory InnerProductSpace

namespace DDROFB

/-- **Theorem 6 (corrected: thresholds that make `P^FB` a `1 − α` confidence region).**
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 6, p. 19:
"Suppose `P∗` has independent components and bounded support. With probability `1 − α` with
respect to the sample, the family `{U^FB_ϵ : 0 < ϵ < 1}` simultaneously implies a probabilistic
guarantee for `P∗`, where `U^FB_ϵ` = (23). Moreover, `δ∗(v| U^FB_ϵ)` = (24)." (Proof on p. ec5 =
PDF p. 43.)

**Formalization Note.** The sample is `S : Fin N → ℝ^d` under the product measure
`Measure.pi (fun _ => Pstar)` (p. 6). The paper's thresholds `t_i, σ̄_fi, σ̄_bi` are bootstrapped
(Algorithm 1), which makes the first clause false for small samples (the paper itself calls such
tests "only asymptotically valid", p. 8). They are replaced by arbitrary functions
`mb, mf, σf, σb` of the sample with the coverage hypothesis `hcov`: `P^FB` built from them
contains `P∗` with probability at least `1 − α` — the confidence-region property (p. 9) that the
proof uses through Theorem 3. `m_b = μ̂ − t ≤ μ̂ + t = m_f` is generalized to any `mb ≤ mf`;
`σf, σb > 0` because (23) divides by them. The quantifier over `0 < ε < 1` is inside the event
(simultaneity). The support function is stated as `IsLUB`. Bounded support is
`∃ R, ‖ũ‖ ≤ R` almost surely. -/
theorem theorem_6_fb_sets {d N : ℕ} (Pstar : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure Pstar] (hind : HasIndepComponents Pstar)
    (hbdd : ∃ R : ℝ, ∀ᵐ u ∂Pstar, ‖u‖ ≤ R)
    (α : ℝ) (mb mf σf σb : (Fin N → EuclideanSpace ℝ (Fin d)) → Fin d → ℝ)
    (hm : ∀ S i, mb S i ≤ mf S i) (hσf : ∀ S i, 0 < σf S i) (hσb : ∀ S i, 0 < σb S i)
    (hcov : 1 - α ≤ (Measure.pi (fun _ : Fin N => Pstar)
        {S | Pstar ∈ PFB (mb S) (mf S) (σf S) (σb S)}).toReal) :
    1 - α ≤ (Measure.pi (fun _ : Fin N => Pstar)
        {S | SimultaneouslyImplies (fun ε => UFB (mb S) (mf S) (σf S) (σb S) ε) Pstar}).toReal ∧
    ∀ S : Fin N → EuclideanSpace ℝ (Fin d), ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ v : EuclideanSpace ℝ (Fin d),
        IsLUB ((fun u => ⟪v, u⟫_ℝ) '' UFB (mb S) (mf S) (σf S) (σb S) ε)
          (fbBound (mb S) (mf S) (σf S) (σb S) ε v) := by sorry

end DDROFB
