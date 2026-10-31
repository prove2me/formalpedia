-- Prove2me | Theorems.Thm_CompetingKS_lemma_1
-- name    : CompetingKS.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:28.98148+00:00
-- url     : https://prove2.me/theorems/4b569c1d-cc37-4cd3-9623-3caa6986c246
-- title:
--   Lemma 1 — retail quantities and prices in the one-to-two and two-to-one channels ($\eta<1$ in the latter)
-- statement:
--   Let $b>0$, $\eta\in[0,1]$, and let $w_i\le a$, $w_j<a$. Write $x=a-w_i$, $y=a-w_j$.
--
--   1. **One-to-two channel.** The pair $(q^*_i(w),q^*_j(w))$ is the unique pure Nash equilibrium on $q\ge0$ of the two retailers' quantity game, and
--      - if $x/y\le\eta/2$, then $p^*_i(w)=\frac{2a-\eta y}2$ and $q^*_i(w)=0$;
--      - if $\eta/2<x/y<2/\eta$, then $p^*_i(w)=w_i+\frac{2x-\eta y}{4-\eta^2}$ and $q^*_i(w)=\frac{2x-\eta y}{b(4-\eta^2)}$;
--      - if $x/y\ge2/\eta$, then $p^*_i(w)=\frac{a+w_i}2$ and $q^*_i(w)=\frac{x}{2b}$.
--   2. **Two-to-one channel.** Let in addition $\eta<1$. The pair $(q^*_i(w),q^*_j(w))$ is the unique maximizer on $q\ge0$ of the common retailer's total profit, and
--      - if $x/y\le\eta$, then $p^*_i(w)=\frac{2a-\eta y}2$ and $q^*_i(w)=0$;
--      - if $\eta<x/y<1/\eta$, then $p^*_i(w)=\frac{a+w_i}2$ and $q^*_i(w)=\frac{x-\eta y}{2b(1-\eta^2)}$;
--      - if $x/y\ge1/\eta$, then $p^*_i(w)=\frac{a+w_i}2$ and $q^*_i(w)=\frac{x}{2b}$.
--
--   This solves the retail stage, so every profit in the two bargaining problems is an explicit piecewise function of the contracts.
--
--   Differences from the source:
--   - reading: the retailers "set" the quantities → the quantities are the unique Nash equilibrium of the quantity game on q ≥ 0, resp. the unique maximizer of the common retailer on q ≥ 0; reason: this is the retail stage the lemma solves; uniqueness is the stronger reading
--   - encoding: contracts w = (wᵢ, wⱼ) with the ratio (a − wᵢ)/(a − wⱼ) → wᵢ ≤ a, wⱼ < a; reason: the ratios need a − wⱼ ≠ 0; contracts lie below a (p.15)
--   - encoding: case conditions as ratios, with 2/η and 1/η → the same conditions with cleared denominators; reason: the ratios divide by η and by a − wⱼ; the cleared forms agree with the printed ones wherever those are defined and read 2/η as +∞ at η = 0, which changes no instance
--   - encoding: η ∈ [0, 1] for the two-to-one channel → η ∈ [0, 1); reason: at η = 1, wᵢ = wⱼ < a Lemma 1(ii)(a) gives q*ᵢ = 0 and (ii)(c) gives q*ᵢ = (a − wᵢ)/(2b), and (ii)(b) divides by 1 − η² = 0, so q* and the profits are undefined there; this excludes only that undefined case
-- source:
--   Feng, Li, Shanthikumar, Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution, accepted manuscript (Management Science, July 3, 2021), SSRN 3447674, Lemma 1, pp.13–14

import Mathlib
import Definitions.Def_CompetingKS_qOT

open scoped NNReal

namespace CompetingKS

/-- Lemma 1 (Retail Quantities and Prices), Feng, Li, Shanthikumar, *Negotiations in Competing
Supply Chains: The Kalai-Smorodinsky Bargaining Solution*, accepted manuscript (Management Science,
July 3, 2021), SSRN 3447674, pp.13–14.

For `wᵢ ≤ a`, `wⱼ < a`: part (i), the one-to-two channel: `qOT` gives the unique Nash equilibrium of the
retailers' quantity game, and the quantities and prices are as in cases (a), (b), (c). Part (ii),
the two-to-one channel with `η < 1`: `qTO` gives the unique optimum of the common retailer, and the
quantities and prices are as in cases (a), (b), (c).

**Formalization Note** The case conditions are written with cleared denominators; `wⱼ < a` is what
makes the printed ratios defined (by symmetry of the channel, the roles of `i`, `j` may be swapped). Part (ii) carries `η < 1`: at `η = 1`, `wᵢ = wⱼ` the printed
cases (a) and (c) both apply with different `q*ᵢ`. -/
theorem lemma_1 {a b η wi wj : ℝ} (hb : 0 < b) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hwi : wi ≤ a) (hwj : wj < a) :
    ((∀ qi qj : ℝ≥0, IsRetailEqOT a b η wi wj qi qj ↔
        (qi : ℝ) = qOT a b η wi wj ∧ (qj : ℝ) = qOT a b η wj wi) ∧
      (2 * (a - wi) ≤ η * (a - wj) →
        priceOT a b η wi wj = (2 * a - η * (a - wj)) / 2 ∧ qOT a b η wi wj = 0) ∧
      (η * (a - wj) < 2 * (a - wi) → η * (a - wi) < 2 * (a - wj) →
        priceOT a b η wi wj = wi + (2 * (a - wi) - η * (a - wj)) / (4 - η ^ 2) ∧
        qOT a b η wi wj = (2 * (a - wi) - η * (a - wj)) / (b * (4 - η ^ 2))) ∧
      (2 * (a - wj) ≤ η * (a - wi) →
        priceOT a b η wi wj = (a + wi) / 2 ∧ qOT a b η wi wj = (a - wi) / (2 * b))) ∧
    (η < 1 →
      (∀ qi qj : ℝ≥0, IsRetailOptTO a b η wi wj qi qj ↔
        (qi : ℝ) = qTO a b η wi wj ∧ (qj : ℝ) = qTO a b η wj wi) ∧
      (a - wi ≤ η * (a - wj) →
        priceTO a b η wi wj = (2 * a - η * (a - wj)) / 2 ∧ qTO a b η wi wj = 0) ∧
      (η * (a - wj) < a - wi → η * (a - wi) < a - wj →
        priceTO a b η wi wj = (a + wi) / 2 ∧
        qTO a b η wi wj = ((a - wi) - η * (a - wj)) / (2 * b * (1 - η ^ 2))) ∧
      (a - wj ≤ η * (a - wi) →
        priceTO a b η wi wj = (a + wi) / 2 ∧ qTO a b η wi wj = (a - wi) / (2 * b))) := by sorry

end CompetingKS
