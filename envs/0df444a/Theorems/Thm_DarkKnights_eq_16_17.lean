-- Prove2me | Theorems.Thm_DarkKnights_eq_16_17
-- name    : DarkKnights.eq_16_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:36.548105+00:00
-- url     : https://prove2.me/theorems/f8b99149-8f41-411f-8aac-1fbc30071b5f
-- title:
--   Eqs. (16)–(17) with (10) — $b^*(k)=Zk^\alpha$ and $k^*=(\alpha Z/2)^{1/(1-\alpha)}=k_{FB}$
-- statement:
--   Let $\alpha\in(0,1)$, $Z>0$, $\tau\in[0,1)$, let $\sigma(k,b)$ be a dealer strategy that is optimal at $h=1$ after every $k,b\ge0$, and write $V(k,b)$ for the firm value (15) at $h=1$. Then
--
--   1. for every $k\ge0$, $b^*(k)=Zk^\alpha$ maximizes $b\mapsto V(k,b)$ over $b\ge0$ (16);
--   2. $k^*=\left(\frac{\alpha Z}{2}\right)^{\frac1{1-\alpha}}$ maximizes $k\mapsto V(k,b^*(k))$ over $k\ge0$ (17);
--   3. the same $k^*$ maximizes the first-best objective $k\mapsto\int_0^Z zk^\alpha\,d\Gamma(z)-k$ over $k\ge0$, so $k^*=k_{FB}$ of (10).
--
--   With an intervening dealer the firm borrows up to its largest asset value and invests at the first-best level.
--
--   Differences from the source:
--   - reading: the first-order conditions yield $b^*(k)$ and $k^*$ → $b^*(k)$ and $k^*$ are maximizers (not unique: every $b\ge Zk^\alpha$ gives the same value); reason: footnote 18 (p.21): for $b\ge Zk^\alpha$ the taxed region is empty
--   - reading: (10): the first-best level of capital would be $k_{FB}$ → $k^*$ maximizes $\mathbb E[a(z,k)]-k$ over $k\ge0$; reason: first best means no frictions: no taxes, no liquidation, no renegotiation
--   - generalization: the value under the dealer's strategy of Lemmas 2–3 (Appendices A, D for other hedge ratios) → the value under every dealer-optimal strategy $\sigma$; reason: the paper's strategy is dealer-optimal, so this specializes to it; all optimal offers give every player the same payoff except at the indifference point $a=b-hb$, a null set of states (at $h\ge1$, $a\ge b$ the dealer is indifferent among offers with identical payoffs)
--   - reading: the CDS spread makes the protection seller break even including the equity injection (p.18) → premium $=-\mathbb E[\text{dealer's ex-post payoff}]$; reason: zero NPV for the protection seller (p.8); equals Lemma 4's bracket on the equilibrium path
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §2, eqs. (16)–(17), p.20 (PDF 22); eq. (10), p.12 (PDF 14)

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveSellerModel

open MeasureTheory

namespace DarkKnights

/-- **Eqs. (16)–(17), with (10)** (optimal debt and capital in the active-CDS-seller model reach
the first best).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §2, eqs. (16)–(17), p.20 (PDF p.22); eq. (10), p.12 (PDF p.14).

Let `σ k b` be a dealer strategy that is optimal at `h = 1` after every `k, b ≥ 0`, and
`V(k, b) = V(k, b, 1)` the firm value (15). Then
1. (16) for every `k ≥ 0`, `b*(k) = Z k^α` maximizes `b ↦ V(k, b)` over `b ≥ 0`;
2. (17) `k* = (αZ/2)^{1/(1−α)}` maximizes `k ↦ V(k, b*(k))` over `k ≥ 0`;
3. (10) the same `k*` maximizes the first-best objective `k ↦ ∫_0^Z z k^α dΓ − k` over `k ≥ 0`,
   i.e. `k* = k_FB`.

**Formalization Note** `(αZ/2)^{1/(1−α)}` is `Real.rpow`. Maximizers, not unique maximizers:
every `b ≥ Z k^α` gives the same value (footnote 18, p.21). -/
theorem eq_16_17 (α Z τ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hZ : 0 < Z) (hτ0 : 0 ≤ τ)
    (hτ1 : τ < 1) (σ : ℝ → ℝ → ℝ → ℝ × ℝ)
    (hσ : ∀ k b : ℝ, 0 ≤ k → 0 ≤ b → IsDealerOptimal α Z k b 1 (σ k b)) :
    let kstar : ℝ := (α * Z / 2) ^ (1 / (1 - α))
    (∀ k : ℝ, 0 ≤ k → ∀ b : ℝ, 0 ≤ b →
        firmValue2 α Z τ k b 1 (σ k b) ≤ firmValue2 α Z τ k (Z * k ^ α) 1 (σ k (Z * k ^ α))) ∧
      (∀ k : ℝ, 0 ≤ k →
        firmValue2 α Z τ k (Z * k ^ α) 1 (σ k (Z * k ^ α))
          ≤ firmValue2 α Z τ kstar (Z * kstar ^ α) 1 (σ kstar (Z * kstar ^ α))) ∧
      (∀ k : ℝ, 0 ≤ k →
        (1 / Z) * (∫ z in Set.Icc (0 : ℝ) Z, z * k ^ α) - k
          ≤ (1 / Z) * (∫ z in Set.Icc (0 : ℝ) Z, z * kstar ^ α) - kstar) := by sorry

end DarkKnights
