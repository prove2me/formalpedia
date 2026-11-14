-- Prove2me | Theorems.Thm_BilateralProfit_lemma_4_5
-- name    : BilateralProfit.lemma_4_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T02:20:16.247752+00:00
-- url     : https://prove2.me/theorems/e5900b43-a635-4d0b-9307-2e3969a708e7
-- title:
--   Lemma 4.5 — inexpensive detection (corrected: $K\ge2$)
-- statement:
--   There is a constant $C$ such that for every $K\ge2$, every distribution $\rho$ on $G_K\times\mathcal A$ and every $x\in(0,1]$ there are non-negative weights $n_x(a)$, $a\in\mathcal A$, depending only on $\rho$ and $x$, such that
--
--   1. $$\sum_{a\in\mathcal A}n_x(a)\big(\Delta_\rho(a^\star,a)+x\big)\le C\log^3K\Big(\frac Kx+\frac{\log^3K}{x^2}\Big),$$ where $a^\star$ is optimal according to $\rho$; and
--   2. for every random valuation $\tilde V$ on $[0,1]^2$ with probability function of trade $P$ such that $\max_{a\in\mathcal A}\mathbb E[\mathrm{Profit}(\tilde V,a)]\ge\mathbb E_\rho[\mathrm{Profit}(V,a^\star)]+x$,
--   $$\sum_{a\in\mathcal A}n_x(a)\big(P(a)-P_0(a)\big)^2\ge1,$$
--   with $P_0$ the trade function induced by $\rho$.
--
--   The same weights work for every such $P$ once $\rho$ and $x$ are fixed. The lemma drives the proof by contradiction of the information inequality (Theorem 4.2).
--
--   **Formalization Note** $\mathbb E_\rho[\mathrm{Profit}(V,a^\star)]$ is the maximum of the marginal expected profits over $\mathcal A$. A random valuation is a probability measure carried by $[0,1]^2$, with $\mathbb E[\mathrm{Profit}(\tilde V,(p,q))]=(q-p)P(p,q)$. Logarithms are natural.
--
--   Differences from the source:
--   - correction: every $K$ → $K\ge2$; reason: at $K=1$ the right side of 1 is $0$; with $\rho$ concentrated on valuation $(1,1)$ and $x=1$, every gap is $0$, so 1 forces $n_x\equiv0$, but $\tilde V\equiv(0,1)$ has profit $1\ge0+x$ at $a=(0,1)$ while the sum in 2 is $0<1$; every use in the paper has $K\ge2$
--   - reading: "for some constant $C$" after "for every distribution $\rho$ … and $x$" → $C$ chosen before $K$, $\rho$ and $x$; reason: the proof of Theorem 4.2 uses one $C$ for every $K$ and $\rho$ ("when $C_0\ge32(C+1)$")
--   - encoding: a random valuation $\tilde V$ with probability function of trade $P$; $a^\star$ optimal according to $\rho$ → a probability measure on $\mathbb R^2$ carried by $[0,1]^2$; $\Delta_\rho(a^\star,\cdot)$ and $\mathbb E_\rho[\mathrm{Profit}(V,a^\star)]$ through the maximum value `optVal`; reason: same instances; the gap does not depend on the maximizer
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Lemma 4.5, p.20 (PDF 22), restated p.23 (PDF 25); proof pp.28–29 (PDF 30–31)

import Mathlib
import Definitions.Def_BilateralProfit_Analysis

namespace BilateralProfit

open MeasureTheory

/-- **Lemma 4.5 (Inexpensive Detection)**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript,
sha256 e91e8127…), p.20 (PDF 22), restated p.23 (PDF 25); corrected: `K ≥ 2`.

There is a constant `C` such that for every `K ≥ 2`, every distribution `ρ` on `G_K × 𝒜` and every
`x ∈ (0, 1]` there are non-negative weights `n_x(a)`, depending only on `ρ` and `x`, with
1. `Σ_{a ∈ 𝒜} n_x(a)(Δ_ρ(a⋆, a) + x) ≤ C log³K (K/x + log³K/x²)`, and
2. for every random valuation `Ṽ` on `[0,1]²` with trade function `P` such that
   `max_{a ∈ 𝒜} E[Profit(Ṽ, a)] ≥ E_ρ[Profit(V, a⋆)] + x`:
   `Σ_{a ∈ 𝒜} n_x(a)(P(a) − P0(a))² ≥ 1`.

**Formalization Note.** `a⋆` is optimal for the valuation marginal of `ρ`; `Δ_ρ(a⋆, ·)` and
`E_ρ[Profit(V, a⋆)]` do not depend on the choice (`gapStar`, `optVal`). `C` is chosen before
`K`, `ρ`, `x`; the weights before the law of `Ṽ`. `log` is natural. The printed lemma has no
lower bound on `K`; at `K = 1` it is false (see the item's differences). -/
theorem lemma_4_5 :
    ∃ C : ℝ, ∀ K : ℕ, 2 ≤ K → ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∀ x : ℝ, 0 < x → x ≤ 1 →
        ∃ n : Act K → ℝ, (∀ a, 0 ≤ n a) ∧
          ∑ a, n a * (gapStar ρ a + x) ≤
            C * Real.log K ^ 3 * ((K : ℝ) / x + Real.log K ^ 3 / x ^ 2) ∧
          ∀ μ : Measure (ℝ × ℝ), IsValLaw μ →
            (∃ a : Act K, optVal ρ + x ≤ muP μ (pt K a.1)) →
              1 ≤ ∑ a, n a * (Ptrade μ (pt K a.1) - P0 ρ (pt K a.1)) ^ 2 := by sorry

end BilateralProfit
