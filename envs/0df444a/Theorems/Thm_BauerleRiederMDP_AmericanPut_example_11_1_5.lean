-- Prove2me | Theorems.Thm_BauerleRiederMDP_AmericanPut_example_11_1_5
-- name    : BauerleRiederMDP.AmericanPut.example_11_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:38.695939+00:00
-- url     : https://prove2.me/theorems/f5a53fcc-4469-4c9f-81ca-6266ee6915b5
-- title:
--   Example 11.1.5 — explicit perpetual put for $i=1/4$, $u=2$, $d=1/2$ (corrected: on the price lattice $\{K2^k\}$)
-- statement:
--   Take the binomial market with $i=0.25$, $u=2$, $d=\tfrac12$ and a strike $K>0$. Then $\beta=(1+i)^{-1}=\tfrac45$, $q=\tfrac12$, and the fixed point equation of the perpetual put reads
--   $$P(x)=\max\Big\{K-x,\ \tfrac25\big(P(2x)+P(\tfrac12x)\big)\Big\}.$$
--   Let
--   $$\hat P(x)=\begin{cases}K-x, & x\le \tfrac K2,\\[2pt] \dfrac{K^2}{4x}, & x>\tfrac K2,\end{cases}\qquad L_K=\{K\,2^k\mid k\in\mathbb Z\}.$$
--   Then:
--
--   1. $\beta=\tfrac45$ and $q=\tfrac12$;
--   2. $\hat P$ solves the fixed point equation at every $x\in L_K$;
--   3. $\hat P$ is the unique bounded solution on $L_K$: every $w$ bounded on $L_K$ that solves the equation at every point of $L_K$ equals $\hat P$ on $L_K$;
--   4. $P(x)=\hat P(x)$ for every $x\in L_K$, where $P$ is the price of the perpetual put;
--   5. for $x\in L_K$: $x\in E^*$ if and only if $x\le K/2$;
--   6. it is optimal to exercise when the stock falls below $x^*=K/2$: for every $x\in L_K$ the time $\tau^*=\inf\{n\in\mathbb N_0\mid S_n\le K/2\}$ is a stopping time whose expected discounted payoff is the supremum over all stopping times;
--   7. $\mathbb Q_x(\tau^*<\infty)=1$ for every $x\in E$.
--
--   The example gives a closed form of the perpetual put on the prices reachable from a lattice starting point, and shows that the optimal exercise time is almost surely finite here because $\log_2 S_n$ is a symmetric random walk.
--
--   **Formalization Note** The lattice $L_K$ is closed under $x\mapsto 2x$ and $x\mapsto x/2$, so a stock started on it stays on it.
--
--   Differences from the source:
--   - correction: P̂ is the unique bounded solution of the fixed point equation and the price, with exercise below x* = K/2, on all of E = ℝ₊ → these claims (2–6) on the lattice L_K = {K 2^k | k ∈ ℤ}; reason: at x = 3K/4, P̂(x) = K/3 but the right-hand side is max{K/4, 19K/60} = 19K/60; the true price there is 5K/16 and on ℝ₊ the exercise region is [0, 2K/3]; on L_K (closed under the moves) the book's claims hold
--   - reading: strike K (sign not stated) → hypothesis 0 < K; reason: a strike price is positive; K²/(4x) and K/2 need K > 0
--   - reading: 'it is optimal to exercise when the stock falls below x* = K/2' → E* ∩ L_K = {x ∈ L_K | x ≤ K/2} and the hitting time of [0, K/2] attains the supremum from every x ∈ L_K; reason: both the exercise region and the exercise rule are what the sentence describes
--   - encoding: 𝔼^ℚ_x and sup_τ as real numbers, on the probability space of the market → lower Lebesgue integrals in ℝ≥0∞ on the coin space ℕ → Bool under the product law pathLaw; P is toReal of the ℝ≥0∞ supremum; reason: the integrand is nonnegative and bounded by K on E, so the supremum is finite and the values agree
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, Example 11.1.5, pp.339–340, PDF 347–348

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_policyTime
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_exerciseRegion
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_q

open MeasureTheory
open scoped ENNReal

namespace BauerleRiederMDP.AmericanPut

/-- **Example 11.1.5** (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011),
pp.339–340, PDF 347–348), corrected to the price lattice `L_K = {K 2^k | k ∈ ℤ}`: for `i = 0.25`, `u = 2`,
`d = 1/2` one has `β = 4/5`, `q = 1/2`; the fixed point equation is
`P(x) = max{K − x, (2/5)(P(2x) + P(x/2))}`; the function `P(x) = K − x` for `x ≤ K/2`, `P(x) = K²/(4x)` for
`x > K/2` is, on `L_K`, the unique bounded solution of this equation and the price of the perpetual put; it
is optimal to exercise when the stock falls below `x* = K/2`; and `τ* = inf{n ∈ ℕ₀ | S_n ≤ x*}` satisfies
`ℙ_x(τ* < ∞) = 1` for all `x ∈ E`.

**Formalization Note.** The book states the fixed point and value claims on all of `E = ℝ₊`, where they are
false (at `x = 3K/4` the displayed `P` gives `K/3`, the right-hand side of the equation gives `19K/60`, and the
price of the put is `5K/16`; `E* = [0, 2K/3]`). Starting from a lattice price the stock stays on `L_K`, and there
the book's formula, its uniqueness and the exercise rule hold; the statement is restricted to `L_K` for these
claims (Figure 11.1 is drawn on prices with `K/2` on the lattice). The last claim holds on all of `E`. -/
theorem example_11_1_5 (M : BinomialMarket) (hi : M.i = 1 / 4) (hu : M.u = 2) (hd : M.d = 1 / 2)
    (K : ℝ) (hK : 0 < K) :
    let Pex : ℝ → ℝ := fun x => if x ≤ K / 2 then K - x else K ^ 2 / (4 * x)
    let L : Set ℝ := {x : ℝ | ∃ k : ℤ, x = K * (2 : ℝ) ^ k}
    (M.beta = 4 / 5 ∧ M.q = 1 / 2) ∧
    (∀ x ∈ L, Pex x = max (K - x) (2 / 5 * (Pex (2 * x) + Pex (1 / 2 * x)))) ∧
    (∀ w : ℝ → ℝ, (∃ C : ℝ, ∀ x ∈ L, |w x| ≤ C) →
      (∀ x ∈ L, w x = max (K - x) (2 / 5 * (w (2 * x) + w (1 / 2 * x)))) → ∀ x ∈ L, w x = Pex x) ∧
    (∀ x ∈ L, M.perpetualPut K x = Pex x) ∧
    (∀ x ∈ L, (x ∈ M.exerciseRegion K ↔ x ≤ K / 2)) ∧
    (∀ x ∈ L, IsStoppingTime (M.policyTime x (fun _ => Set.Iic (K / 2))) ∧
      M.putReward K x (M.policyTime x (fun _ => Set.Iic (K / 2))) =
        ⨆ τ : {τ : (ℕ → Bool) → ℕ∞ // IsStoppingTime τ}, M.putReward K x τ.1) ∧
    (∀ x : ℝ, 0 ≤ x → M.pathLaw {ω | M.policyTime x (fun _ => Set.Iic (K / 2)) ω = ⊤} = 0) := by sorry

end BauerleRiederMDP.AmericanPut
