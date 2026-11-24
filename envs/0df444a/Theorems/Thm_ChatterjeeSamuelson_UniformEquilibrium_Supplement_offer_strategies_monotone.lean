-- Prove2me | Theorems.Thm_ChatterjeeSamuelson_UniformEquilibrium_Supplement_offer_strategies_monotone
-- name    : ChatterjeeSamuelson.UniformEquilibrium.Supplement.offer_strategies_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:57:14.751178+00:00
-- url     : https://prove2.me/theorems/70f1ff2b-b65e-4b02-b6ce-754ff8c8ba08
-- title:
--   Theorem 1 (corrected: 0 < k for the buyer, k < 1 for the seller, positive trade probability) — equilibrium offer strategies are increasing in the reservation price
-- statement:
--   Consider the sealed-offer bargaining game: a seller with reservation price $v_s$ asks $s$, a buyer with reservation price $v_b$ offers $b$, and the good is traded if and only if $b\ge s$, at the price $kb+(1-k)s$, where $0\le k\le 1$. The buyer's belief about $v_s$ is a probability measure $\mu_b$ on $\mathbb R$, the seller's belief about $v_b$ is a probability measure $\mu_s$, and the reservation prices range over $[\underline v_s,\bar v_s]$ and $[\underline v_b,\bar v_b]$. Let $(S,B)$ be a Bayesian equilibrium pair of measurable offer strategies, with $S$ integrable for $\mu_b$ and $B$ integrable for $\mu_s$. Write
--
--   $$
--   G(b)=\mu_b\{v_s : S(v_s)\le b\},\qquad H(s)=\mu_s\{v_b : s\le B(v_b)\}
--   $$
--
--   for the probability that the buyer's offer $b$, respectively the seller's ask $s$, leads to trade. Then:
--
--   1. **Buyer.** If $k>0$, then for all $v<v'$ in $[\underline v_b,\bar v_b]$ with $G(B(v))>0$ or $G(B(v'))>0$,
--   $$B(v)\le B(v').$$
--   2. **Seller.** If $k<1$, then for all $v<v'$ in $[\underline v_s,\bar v_s]$ with $H(S(v))>0$ or $H(S(v'))>0$,
--   $$S(v)\le S(v').$$
--
--   A player who values the good more asks (offers) a weakly higher price, as long as the offers compared can lead to trade. The result holds for every equilibrium, without continuity or differentiability of the strategies, and is the structural fact behind the class $\underline A$ restriction of Theorems 2 and 3.
--
--   **Formalization Note** Expected profits are the mission's $\pi_b$ and $\pi_s$, written as integrals against the opponent's value distribution (ties trade). They are Bochner integrals, which Lean sets to $0$ for non-integrable integrands, so measurability and integrability of the strategies are assumed; the paper's offer distributions have bounded supports. Trade probabilities are measures of sets, compared with $0$ in $[0,\infty]$.
--
--   Differences from the source:
--
--   - correction: the buyer's and the seller's equilibrium strategies are increasing, with no further condition → the buyer half assumes 0 < k and that B(v) or B(v') trades with positive probability; the seller half assumes k < 1 and that S(v) or S(v') trades with positive probability; reason: the printed claim is false in both excluded cases. A type whose offer never trades may offer anything that never trades: Example 1(a) (the mission's goal) admits B(v) = −v on [0, ((1 − k)/2)v̄), which is decreasing. At k = 0 the buyer's price is the seller's ask, so offers in a gap of the seller's asks are payoff-equivalent: with uniform beliefs on [0, 1], S = 1/2 on [0, 1/4], 3/4 on (1/4, 1/2], (1 + v)/2 above, and B(v) = v except B = 0.51 on (1/2, 5/8) and B = 1/2 on [5/8, 3/4) is an equilibrium in which B(0.55) > B(0.7) and both offers trade with probability 1/4; k = 1 is symmetric for the seller. The proof's step "a buyer holding v_b could lower his offer to b′ and increase his profit" gains k(b − b′)G(b), positive exactly under the added premises, and §2 (p. 839) restricts to equilibria in which agreement occurs with positive probability
--   - reading: "increasing" → weakly increasing, B(v) ≤ B(v') and S(v) ≤ S(v'); reason: the proof concludes b′ ≥ b, and the paper's own constant-offer equilibrium (p. 849) is not strictly increasing
--   - generalization: beliefs F_b, F_s strictly increasing and differentiable on the value intervals (pp. 837–838) → beliefs are arbitrary probability measures on ℝ; reason: the paper states the proof "requires no special assumptions"; the paper's beliefs are the probability measures with those distribution functions, so the statement specializes to the source's
--   - encoding: expected profits against the offer densities g_b, g_s (equation (1), p. 838; p. 839) → expected profits against the opponent's value distribution, for measurable strategies S, B integrable for μb, μs; reason: the two forms agree whenever the offer densities exist, and integrability only excludes strategies for which the paper's profit integrals are undefined
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), https://doi.org/10.1287/opre.31.5.835, p. 839 [PDF 5], Theorem 1; proof pp. 839–840 [PDF 5–6], display (2); §2 standing restriction to equilibria with trade, p. 839 [PDF 5]

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_Shared_buyerProfit
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerProfit
import Definitions.Def_ChatterjeeSamuelson_Shared_IsEquilibrium

open MeasureTheory ProbabilityTheory Set

namespace ChatterjeeSamuelson.UniformEquilibrium.Supplement

/-- Theorem 1 (corrected) (Chatterjee & Samuelson, *Bargaining under Incomplete
Information*, Oper. Res. 31(5) 1983, §2, Theorem 1, p. 839 [PDF 5]; proof pp. 839–840
[PDF 5–6]): "Under the sealed offer bargaining rule, the equilibrium bargaining strategies of
the buyer and seller are increasing in the respective reservation prices."

Let `(S, B)` be an equilibrium (`Shared.IsEquilibrium`) of the sealed-offer game with split
`k ∈ [0, 1]`, buyer belief `μb` about the seller's value and seller belief `μs` about the
buyer's value, values ranging over `[loS, hiS]` (seller) and `[loB, hiB]` (buyer). Write
`G(b) = μb {x | S x ≤ b}` (probability that the buyer's offer `b` trades) and
`H(s) = μs {x | s ≤ B x}` (probability that the seller's ask `s` trades). Then

1. (buyer) if `0 < k`, for buyer values `v < v'` in `[loB, hiB]` such that one of the two
   offers `B v`, `B v'` trades with positive probability, `B v ≤ B v'`;
2. (seller) if `k < 1`, for seller values `v < v'` in `[loS, hiS]` such that one of the two
   asks `S v`, `S v'` trades with positive probability, `S v ≤ S v'`.

*Formalization Note.* "Increasing" is weak monotonicity: the proof concludes `b' ≥ b`, and
the paper's constant equilibrium (p. 849) is not strictly increasing. The printed theorem is
false without the two premises added here (see the mission's DISPROOF record): a type whose
offer trades with probability zero may offer anything that never trades (Example 1(a) allows
a decreasing `B` below `((1 − k)/2) v̄`), and at `k = 0` (buyer) or `k = 1` (seller) the
price does not depend on one's own offer, so offers inside a gap of the opponent's offers are
payoff-equivalent and an equilibrium with uniform beliefs and a non-monotone `B` exists. The
premises are exactly those the paper's proof uses: the step "lower his offer to b′ and
increase his profit" gains `k (b − b') G(b)`, positive only when `k > 0` and `G(b) > 0`; §2
restricts to equilibria in which trade occurs with positive probability.
Beliefs are arbitrary probability measures (the paper's strictly increasing differentiable
distribution functions are a special case; the proof "requires no special assumptions").
`Measurable S`, `Measurable B`, `Integrable S μb`, `Integrable B μs` are added because the
expected profits are Bochner integrals, which are `0` for non-integrable integrands; the
paper's offer distributions have bounded supports. -/
theorem offer_strategies_monotone (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (μb μs : Measure ℝ) [IsProbabilityMeasure μb] [IsProbabilityMeasure μs]
    (loS hiS loB hiB : ℝ) (S B : ℝ → ℝ)
    (hSmeas : Measurable S) (hBmeas : Measurable B)
    (hSint : Integrable S μb) (hBint : Integrable B μs)
    (heq : Shared.IsEquilibrium k μb μs loS hiS loB hiB S B) :
    (∀ v ∈ Icc loB hiB, ∀ v' ∈ Icc loB hiB, v < v' → 0 < k →
        (0 < μb {x | S x ≤ B v} ∨ 0 < μb {x | S x ≤ B v'}) → B v ≤ B v') ∧
      (∀ v ∈ Icc loS hiS, ∀ v' ∈ Icc loS hiS, v < v' → k < 1 →
        (0 < μs {x | S v ≤ B x} ∨ 0 < μs {x | S v' ≤ B x}) → S v ≤ S v') := by sorry

end ChatterjeeSamuelson.UniformEquilibrium.Supplement
