-- Prove2me | Theorems.Thm_AssortRotation_Concealment_lemma_4
-- name    : AssortRotation.Concealment.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:13.803167+00:00
-- url     : https://prove2.me/theorems/2d1bd01c-0714-4094-838c-d39d0450e188
-- title:
--   Lemma 4, p. 38 — swapping a top-priced first product with a better-valued second product does not raise revenue
-- statement:
--   Products $(p_1,X_1),(p_2,X_2),\dots,(p_N,X_N)$ are offered sequentially in this order to a consumer with nonnegative, decreasing marginal utility $v$. She buys product $i$ iff $v(k)+X_i-p_i\ge0$, where $k$ is the number of items already bought. All prices are nonnegative, and the first product has the highest price,
--   $$
--   p_1\ \ge\ \max\{p_2,\dots,p_N\}.
--   $$
--   Let $R$ be the retailer's revenue for this sequence, and $\hat R$ the revenue when products 1 and 2 (prices and realized valuations) are interchanged. If $X_1-p_1\le X_2-p_2$, then
--   $$
--   \hat R\ \le\ R .
--   $$
--
--   Moving the higher-valued but cheaper second product ahead of the most expensive one cannot help the retailer. This is the single interchange step of the proof of Theorem 1(a).
--
--   **Formalization Note.** In the paper $\hat R$ interchanges the products only on the event $X_1-p_1\le X_2-p_2$, and $\hat R=R$ elsewhere, so the content of $R\ge\hat R$ is the inequality on that event. The statement is pathwise, for every realization. The consumer starts with no purchases. A mid-sequence use with $k$ prior purchases is the same statement for the shifted sequence $v(\cdot+k)$, which is again nonnegative and decreasing.
-- source:
--   Ferreira & Goh, HBS Working Paper 17-041 (2020 revision), p. 38, Lemma 4

import Mathlib
import Definitions.Def_AssortRotation_Concealment_Model

namespace AssortRotation.Concealment

/-- Lemma 4, p. 38. Let the first product `a₁ = (p₁, X₁)` have the highest price of the
sequence `a₁, a₂, t` (all prices nonnegative). On the event `X₁ − p₁ ≤ X₂ − p₂`, interchanging
the first two products (prices and realized valuations) does not increase the sequential
revenue: `R̂ ≤ R`. (Off that event `R̂ = R` by definition.) -/
theorem lemma_4 (v : ℕ → ℝ) (hv : MarginalUtility v) (a₁ a₂ : ℝ × ℝ) (t : List (ℝ × ℝ))
    (hp : ∀ b ∈ a₁ :: a₂ :: t, 0 ≤ b.1) (h₂ : a₂.1 ≤ a₁.1) (ht : ∀ b ∈ t, b.1 ≤ a₁.1)
    (hX : a₁.2 - a₁.1 ≤ a₂.2 - a₂.1) :
    seqRev v (a₂ :: a₁ :: t) 0 ≤ seqRev v (a₁ :: a₂ :: t) 0 := by sorry

end AssortRotation.Concealment
