-- Prove2me | Theorems.Thm_BilateralProfit_lemma_A_6
-- name    : BilateralProfit.lemma_A_6
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T02:19:14.349965+00:00
-- url     : https://prove2.me/theorems/4885bed2-14bf-4657-b9ca-2d4627856814
-- title:
--   Lemma A.6 — discretization error $2/K$
-- statement:
--   For every integer $K\ge1$ and every $(p,q)\in\mathcal T$ (that is, $0\le p\le q\le1$) there is a pair $(p',q')\in\mathcal A$ such that for every valuation pair $(s,b)$,
--   $$\mathrm{Profit}((s,b),(p,q))\le\mathrm{Profit}((s,b),(p',q'))+\frac2K .$$
--   Consequently, restricting the comparator to $\mathcal A$ adds at most $2T/K$ to regret: for every horizon $T$, valuation sequence and sequence $X_1,\dots,X_T$ of (expected) profits of any algorithm,
--   $$\sum_{t=1}^T\big(\mathrm{Profit}_t(p,q)-X_t\big)\le\sum_{t=1}^T\big(\mathrm{Profit}_t(p',q')-X_t\big)+\frac{2T}K .$$
--
--   Differences from the source:
--   - generalization: every valuation pair $(s_t,b_t)$ (in $[0,1]^2$) → every real pair $(s,b)$; reason: the bound holds for all reals and specializes to $[0,1]^2$
--   - reading: "restricting the comparator to $\mathcal A$ adds at most $2T/K$ to regret" → for every $T$, every valuation sequence and every profit sequence $X_t$ of an algorithm, the regret against $(p,q)$ is at most the regret against $(p',q')$ plus $2T/K$, with the same $(p',q')$; reason: with $X_t=\mathbb E[\mathrm{Profit}_t(p_t,q_t)]$ this gives the sup over $\mathcal T$ at most the sup over $\mathcal A$ plus $2T/K$
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Lemma A.6, p.57 (PDF 59)

import Mathlib
import Definitions.Def_BilateralProfit_Model

namespace BilateralProfit

/-- **Lemma A.6 (Discretization Error)**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript,
sha256 e91e8127…), p.57 (PDF 59): for every integer `K ≥ 1` and every `(p, q) ∈ 𝒯` there is a
pair `(p′, q′) ∈ 𝒜` such that, for every valuation pair `(s_t, b_t)`,
`Profit_t(p, q) ≤ Profit_t(p′, q′) + 2/K`. Consequently, restricting the comparator to `𝒜` adds at
most `2T/K` to regret.

**Formalization Note.** `𝒯 = {0 ≤ p ≤ q ≤ 1}`. The pointwise bound is stated for all real
valuation pairs. The regret consequence is stated for every horizon `T`, every valuation
sequence and every sequence `X_t` of (expected) profits of any algorithm, with the same grid pair
`(p′, q′)`. -/
theorem lemma_A_6 (K : ℕ) (hK : 1 ≤ K) (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    ∃ a' : Act K,
      (∀ s b : ℝ, profit (s, b) (p, q) ≤ profit (s, b) (pt K a'.1) + 2 / K) ∧
      ∀ (T : ℕ) (S : Fin T → ℝ × ℝ) (X : Fin T → ℝ),
        ∑ t, (profit (S t) (p, q) - X t) ≤ ∑ t, (profit (S t) (pt K a'.1) - X t) + 2 * T / K := by sorry

end BilateralProfit
