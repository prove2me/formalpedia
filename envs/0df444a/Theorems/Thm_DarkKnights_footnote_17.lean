-- Prove2me | Theorems.Thm_DarkKnights_footnote_17
-- name    : DarkKnights.footnote_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:48.15727+00:00
-- url     : https://prove2.me/theorems/c6e4809f-3118-462f-b629-425a5b71e9ea
-- title:
--   Footnote 17 — with an intervening dealer the lender's optimal hedge ratio is $h^*=1$ for $b\le Zk^\alpha$
-- statement:
--   Let $\alpha\in(0,1)$, $Z>0$, $k>0$ and $0\le b\le Zk^\alpha$, and let $\sigma(h)$ be a dealer strategy that is optimal after every hedge ratio $h\ge0$. Then
--
--   1. if $b>0$, the value of debt $h\mapsto M(k,b,h)$ is strictly increasing on $[0,1]$;
--   2. $h=1$ maximizes $M(k,b,h)$ over all $h\ge0$.
--
--   This is the lender's step of the backward induction of §2: full hedging is optimal whenever the face value does not exceed the largest asset value $Zk^\alpha$.
--
--   Differences from the source:
--   - reading: $\partial M/\partial h$ is positive for all $h\in[0,1]$ → $M$ strictly increasing on $[0,1]$ when $b>0$; reason: at $b=Zk^\alpha$ the derivative vanishes at the single point $h=1$ and at $b=0$ everywhere; strict monotonicity is what the footnote uses
--   - reading: the optimal hedge ratio is $h^*=1$ (under the conjecture $h\le1$) → $h=1$ maximizes $M$ over all $h\ge0$; reason: §2 allows every $h\ge0$ (p.14) and Appendix A proves the conjecture
--   - generalization: the value under the dealer's strategy of Lemmas 2–3 (Appendices A, D for other hedge ratios) → the value under every dealer-optimal strategy $\sigma$; reason: the paper's strategy is dealer-optimal, so this specializes to it; all optimal offers give every player the same payoff except at the indifference point $a=b-hb$, a null set of states (at $h\ge1$, $a\ge b$ the dealer is indifferent among offers with identical payoffs)
--   - reading: the CDS spread makes the protection seller break even including the equity injection (p.18) → premium $=-\mathbb E[\text{dealer's ex-post payoff}]$; reason: zero NPV for the protection seller (p.8); equals Lemma 4's bracket on the equilibrium path
--   - encoding: the derivative of $M$, with denominator $Zk^\alpha$ → hypothesis $k>0$; reason: the expression is undefined at $k=0$
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §2, p.20 (PDF 22), 'the optimal hedge ratio is h∗ = 1' and footnote 17; Appendix A, pp.41–42

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveSellerModel

namespace DarkKnights

/-- **Footnote 17** (the lender fully hedges in the active-CDS-seller model).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §2, p.20 (PDF p.22): "one can show that the optimal hedge ratio is
h∗ = 1", with footnote 17, p.20; Appendix A, pp.41–42.

For `k > 0` and `0 ≤ b ≤ Z k^α`, and any dealer strategy `σ h` that is optimal after every
hedge ratio `h ≥ 0`:
1. if `b > 0`, the value of debt `h ↦ M(k, b, h)` is strictly increasing on `[0, 1]`;
2. `h = 1` maximizes `M(k, b, h)` over all `h ≥ 0`.

**Formalization Note** The footnote's "∂M/∂h is positive for all h ∈ [0, 1]" is stated as strict
monotonicity on `[0, 1]` (at `b = Z k^α` the derivative vanishes at the single point `h = 1`;
at `b = 0` the value of debt is identically `0`). Hedge ratios above one are covered by
Appendix A. -/
theorem footnote_17 (α Z k b : ℝ) (hα : 0 < α) (hα1 : α < 1) (hZ : 0 < Z) (hk : 0 < k)
    (hb : 0 ≤ b) (hbZ : b ≤ Z * k ^ α) (σ : ℝ → ℝ → ℝ × ℝ)
    (hσ : ∀ h : ℝ, 0 ≤ h → IsDealerOptimal α Z k b h (σ h)) :
    (0 < b → StrictMonoOn (fun h => debtValue2 α Z k b h (σ h)) (Set.Icc (0 : ℝ) 1)) ∧
      ∀ h : ℝ, 0 ≤ h → debtValue2 α Z k b h (σ h) ≤ debtValue2 α Z k b 1 (σ 1) := by sorry

end DarkKnights
