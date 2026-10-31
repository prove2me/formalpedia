-- Prove2me | Theorems.Thm_DarkKnights_eq_8_9
-- name    : DarkKnights.eq_8_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:53.304847+00:00
-- url     : https://prove2.me/theorems/535e2cbb-1bba-4b30-a018-e4c8080c817d
-- title:
--   Eqs. (8)–(9) — active CDS buyer, $b^*(k)=Zk^\alpha\tau/(1+\tau)$ and $k^*=(\alpha Z/(2(1+\tau)))^{1/(1-\alpha)}$
-- statement:
--   In the active-CDS-buyer model, let $\alpha\in(0,1)$, $Z>0$, $\tau\in[0,1)$, let $h(k,b)$ be any lender best response on $[0,1]$ after every $k,b\ge0$, and write $V(k,b)=V(k,b,h(k,b))$. Then
--
--   1. for every $k\ge0$, $b^*(k)=\dfrac{Zk^\alpha\tau}{1+\tau}$ maximizes $b\mapsto V(k,b)$ over all $b\ge0$ (8);
--   2. $k^*=\left(\dfrac{\alpha Z}{2(1+\tau)}\right)^{\frac1{1-\alpha}}$ maximizes $k\mapsto V(k,b^*(k))$ over $k\ge0$ (9).
--
--   Investment stays below the first-best level (10) whenever $\tau>0$.
--
--   Differences from the source:
--   - reading: maximize (7), the firm value at $h=1$, under the conjecture $b\le Zk^\alpha/2$ (footnote 13) → maximize program (2), the firm value at any lender best response, over all $b\ge0$; reason: (8) is the owner's optimal debt in (2); it satisfies the conjecture, and for $b>Zk^\alpha/2$ the best response is $h<1$, where (7) does not apply
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §1, eqs. (8)–(9), p.12 (PDF 14)

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveBuyerModel

namespace DarkKnights

/-- **Eqs. (8)–(9)** (optimal debt and capital in the active-CDS-buyer model).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §1, eqs. (8)–(9), p.12 (PDF p.14).

Let `hfun` be any lender best response (3) on `h ∈ [0, 1]` after every `k, b ≥ 0`, and
`V(k, b) = V(k, b, hfun k b)` the owner's objective (2). Then
1. (8) for every `k ≥ 0`, `b*(k) = Z k^α τ/(1 + τ)` maximizes `b ↦ V(k, b)` over all `b ≥ 0`;
2. (9) `k* = (αZ/(2(1 + τ)))^{1/(1−α)}` maximizes `k ↦ V(k, b*(k))` over `k ≥ 0`.

**Formalization Note** The maximization is over all `b ≥ 0` with the lender's best-response
hedge ratio (program (2)), not only over the range `b ≤ Z k^α/2` where `h = 1` is the best
response; `(·)^{1/(1−α)}` is `Real.rpow`. -/
theorem eq_8_9 (α Z τ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hZ : 0 < Z) (hτ0 : 0 ≤ τ)
    (hτ1 : τ < 1) (hfun : ℝ → ℝ → ℝ)
    (hbr : ∀ k b : ℝ, 0 ≤ k → 0 ≤ b → IsLenderBR1 α Z k b (hfun k b)) :
    let bstar : ℝ → ℝ := fun k => Z * k ^ α * τ / (1 + τ)
    let kstar : ℝ := (α * Z / (2 * (1 + τ))) ^ (1 / (1 - α))
    (∀ k : ℝ, 0 ≤ k → ∀ b : ℝ, 0 ≤ b →
        firmValue1 α Z τ k b (hfun k b) ≤ firmValue1 α Z τ k (bstar k) (hfun k (bstar k))) ∧
      ∀ k : ℝ, 0 ≤ k →
        firmValue1 α Z τ k (bstar k) (hfun k (bstar k))
          ≤ firmValue1 α Z τ kstar (bstar kstar) (hfun kstar (bstar kstar)) := by sorry

end DarkKnights
