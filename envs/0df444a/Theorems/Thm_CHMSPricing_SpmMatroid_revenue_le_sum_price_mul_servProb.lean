-- Prove2me | Theorems.Thm_CHMSPricing_SpmMatroid_revenue_le_sum_price_mul_servProb
-- name    : CHMSPricing.SpmMatroid.revenue_le_sum_price_mul_servProb
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:40:38.842981+00:00
-- url     : https://prove2.me/theorems/718cfb00-8486-4363-ac77-c56ab040b11c
-- title:
--   Lemma 2, p. 5 — the revenue of a truthful mechanism is at most Σ_i p^M_i q^M_i
-- statement:
--   Let $n$ agents have independent values $v_i \sim F_i$ with each $F_i$ regular, and let $M$ be any truthful mechanism (for any downward-closed constraint). Let $q^M_i$ be the probability that $M$ serves agent $i$ and $p^M_i = F_i^{-1}(1 - q^M_i)$. Then
--
--   $$\mathcal R^M \le \sum_{i} p^M_i\, q^M_i.$$
--
--   The bound replaces the optimal revenue by a sum of single-agent posted-price revenues, which is what the posted-price mechanisms of the paper are compared with.
--
--   **Formalization Note** $p^M_i$ is given as an argument with the hypothesis $p^M_i \in [\underline v_i, \overline v_i]$ and $F_i(p^M_i) = 1 - q^M_i$; such a price exists and is unique because $F_i$ is continuous and strictly increasing on the support. Only the first (regular) paragraph of Lemma 2 is stated; the second paragraph (non-regular distributions, randomized prices) is out of scope.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 5, Lemma 2, first paragraph (restated p. 13)

import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Mechanism

namespace CHMSPricing.SpmMatroid

/-- Lemma 2, regular part (p. 5): if every `Fᵢ` is regular, the revenue of any truthful
mechanism `M` is at most `∑ᵢ p^M_i q^M_i`, where `q^M_i` is the probability that `M` serves `i`
and `p^M_i = Fᵢ⁻¹(1 − q^M_i)` (the price in `[loᵢ, hiᵢ]` with `Fᵢ(p^M_i) = 1 − q^M_i`). -/
theorem revenue_le_sum_price_mul_servProb {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular)
    (J : SetSystem ι) (M : Mechanism ι) (hM : IsTruthful D J M)
    (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i) :
    revenue D M ≤ ∑ i, p i * servProb D M i := by sorry

end CHMSPricing.SpmMatroid
