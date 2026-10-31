-- Prove2me | Theorems.Thm_ChenOutlierPricing_General_lemma_EC3
-- name    : ChenOutlierPricing.General.lemma_EC3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:43:23.849317+00:00
-- url     : https://prove2.me/theorems/292046dc-13fb-4a4c-892b-8fec05407312
-- title:
--   Lemma EC.3 — demand estimation at a sampled fixed price
-- statement:
--   In the pricing model (A1)–(A3), let S be a nonempty set of T′ selling periods at whose beginnings the remaining stock is strictly positive, using the inventory timing of equation (2). A fixed feasible price p is offered with probability $q\in(0,1]$ in each selected period. Let $\widehat d$ be the total actual sales in those selected periods at price p. The corruption count within S is at most $\varepsilon T$ almost surely, with ε≥0. Separately, the ambient model has global corruption fraction ρ satisfying $0\le\rho\le T^{-\alpha}$ for fixed α>0, and its global budget holds for every admissible policy. The local budget εT need not be a bound on corruption outside S. Then for every $\delta\in(0,1)$, with probability at least $1-\delta$,
--   $$\left|\frac{\widehat d}{qT'}-f_0(p)\right|\le\min\{1,\varepsilon T/T'\}+\sqrt{\frac{\log(2/\delta)}{qT'}}+\frac{2\log(2/\delta)}{qT'}.$$
--   Sales and noise retain the source's conventions; neither independent noise nor a history-conditioned martingale difference is assumed. The source's bound is retained despite the correlated-noise counterexample recorded separately.
--
--   Differences from the source:
--   - encoding: periods numbered 1 through T with remaining inventory → elapsed indices 0 through T-1 and recursively computed real stock; reason: a bijective time reindexing preserves every price, censored sale and revenue
--   - encoding: randomized seller policies and adaptive outlier curves with E[ξ_t | p_t] = 0 → an independent private uniform tape, arbitrary exogenous probability space, observed-history policy maps, and zero noise integrals on every price-measurable event; reason: random seeds implement stochastic decisions; integrable noise and measurable observations make the printed conditional expectation well defined without a martingale-difference or independent-noise assumption
--   - reading: a fixed price is offered with probability q in every selected period → each corresponding marginal price event has probability q; reason: the printed statement does not say independent draws or add a history-conditioned noise assumption; no stronger condition is inserted
--   - encoding: at most εT corrupted periods within the selected set → a local almost-sure count bound εT, separately from the ambient global budget ρT and (A3); reason: renaming the ambient fraction avoids imposing the local bound on unselected periods
--   - reading: inventory remained positive during the selected selling periods → positive remaining stock at the beginning of each selected period; reason: equation (2) defines the inventory available for a period before its sale; no extra post-sale positivity is imposed
-- source:
--   Chen and Wang, DOI 10.1287/opre.2022.2280, e-companion, p. ec9, Lemma EC.3

import Definitions.Def_ChenOutlierPricing_General_Exploration

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ChenOutlierPricing.General

/-- Chen and Wang, e-companion, ec9, Lemma EC.3. -/
theorem lemma_EC3 (m : Model) (hm : Assumptions m) (T : ℕ) (hT : 0 < T)
    (α : ℝ) (hα : 0 < α)
    {Ξ : Type} [MeasurableSpace Ξ] (π : Policy) (hπ : PolicyAdmissible m.band π) (e : Environment Ξ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (U : Ω → Tape) (V : Ω → Ξ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hfreq : ρ ≤ (T : ℝ)^(-α))
    (hrun : RunAdmissible m π e T (m.x₀*T) (ρ*T) μ U V)
    (S : Finset ℕ) (hS : S ⊆ Finset.range T) (hcard : 0 < S.card)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hcorrupt : ∀ᵐ ω ∂μ, corruptCount m π e T S (U ω) (V ω) ≤ ε*T)
    (hstock : ∀ᵐ ω ∂μ, ∀ t ∈ S,
      0 < stock (m.x₀*T) (trajectory m π e T (m.x₀*T) (U ω) (V ω) t))
    (p q δ : ℝ) (hp : p ∈ Set.Icc m.band.lo m.band.hi)
    (hq : q ∈ Set.Ioc 0 1) (hδ : δ ∈ Set.Ioo 0 1)
    (hprice : ∀ t ∈ S,
      μ.real {ω | (roundAt m π e T (m.x₀*T) (U ω) (V ω) t).price = p} = q) :
    1-δ ≤ μ.real {ω |
      |(∑ t ∈ S,
        let r := roundAt m π e T (m.x₀*T) (U ω) (V ω) t
        if r.price = p then r.sales else 0) / (q*S.card) - m.demand p| ≤
        min 1 (ε*T/S.card) + Real.sqrt (Real.log (2/δ)/(q*S.card)) +
          2*Real.log (2/δ)/(q*S.card)} := by sorry

end ChenOutlierPricing.General
