-- Prove2me | Theorems.Thm_BilateralProfit_eq_17
-- name    : BilateralProfit.eq_17
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T02:20:48.411774+00:00
-- url     : https://prove2.me/theorems/8d306558-66ab-421b-a2d1-b86962104edc
-- title:
--   Eq. (17) — the measure $\nu$ controls profit differences, and $\nu([0,1]^2)=3$
-- statement:
--   Let $P$ be a valuation law on $[0,1]^2$, $\Delta(a',a)=\mathbb E_P[\mathrm{Profit}(V,a')-\mathrm{Profit}(V,a)]$, and $\nu=L\otimes P_b+P_s\otimes L+P$ as in (16). For seller prices $l\le r$ and buyer prices $q_0\le q$ in $[0,1]$,
--   $$\big|\Delta((r,q),(l,q))-\Delta((r,q_0),(l,q_0))\big|\le\nu\big((l,r]\times[q_0,q)\big),$$
--   and the total mass of $\nu$ is $\nu([0,1]^2)=3$.
--
--   In Step 2 of the proof of Lemma 4.8 this is used with $P=P_{P_0}$, the valuation marginal of $\rho$, to choose the buyer blocks (Algorithm 3) and to bound their number.
--
--   **Formalization Note** $E_P[\mathrm{Profit}(V,(p,q))]$ is written $(q-p)P(p,q)$. $L$ is Lebesgue measure on $[0,1]$.
--
--   Differences from the source:
--   - generalization: $P=P_{P_0}$, the valuation marginal of $\rho$ on $G_K$, and grid prices $l,r$ in a seller node, $q_0,q$ in the buyer grid → every valuation law on $[0,1]^2$ and all prices $l\le r$, $q_0\le q$ in $[0,1]$; reason: the marginal of $\rho$ is such a law, and its expected-profit differences are $\Delta_\rho$
--   - encoding: $L$ the Lebesgue measure in $\nu=L\otimes P_{P_0,b}+P_{P_0,s}\otimes L+P_{P_0}$, a measure on $[0,1]^2$ → Lebesgue measure restricted to $[0,1]$; reason: $\nu$ is a measure on $[0,1]^2$, and every set the statement measures lies in $[0,1]^2$, where both give the same value
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), proof of Lemma 4.8, Step 2, p.24 (PDF 26), eqs. (15)–(17)

import Mathlib
import Definitions.Def_BilateralProfit_SellerTree

namespace BilateralProfit

open MeasureTheory

/-- **Equation (17)** and the total mass of `ν`, Brüstle, di Gregorio, Fusco, Leonardi
(manuscript, sha256 e91e8127…), Step 2 of the proof of Lemma 4.8, p.24 (PDF 26).

For a valuation law `P` on `[0,1]²` and `ν = L ⊗ P_b + P_s ⊗ L + P` (16): for seller prices
`l ≤ r` and buyer prices `q₀ ≤ q` in `[0, 1]`,
`|Δ((r, q), (l, q)) − Δ((r, q₀), (l, q₀))| ≤ ν((l, r] × [q₀, q))`, where
`Δ(a′, a) = E_P[Profit(V, a′) − Profit(V, a)]`; and `ν([0,1]²) = 3`.

**Formalization Note.** The paper uses the valuation marginal `P_{P0}` of `ρ` (a law on the
grid) and grid prices in a seller node; the statement holds for every valuation law and all
prices in `[0, 1]`. -/
theorem eq_17 (μ : Measure (ℝ × ℝ)) (hμ : IsValLaw μ) :
    (∀ l r q₀ q : ℝ, l ∈ Set.Icc (0 : ℝ) 1 → r ∈ Set.Icc (0 : ℝ) 1 → q₀ ∈ Set.Icc (0 : ℝ) 1 →
      q ∈ Set.Icc (0 : ℝ) 1 → l ≤ r → q₀ ≤ q →
        |(muP μ (r, q) - muP μ (l, q)) - (muP μ (r, q₀) - muP μ (l, q₀))| ≤
          (nuMeas μ (Set.Ioc l r ×ˢ Set.Ico q₀ q)).toReal) ∧
      nuMeas μ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) = 3 := by sorry

end BilateralProfit
