-- Prove2me | Theorems.Thm_AdWordsMSVV_Tradeoff_theorem_8
-- name    : AdWordsMSVV.Tradeoff.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:28.33999+00:00
-- url     : https://prove2.me/theorems/4e5cf36b-8afb-4d14-81ef-458dc42feb26
-- title:
--   Theorem 8, p. 12 — with ψ_k(i) = Σ_{j≥i} y*_j the discrete tradeoff algorithm is (1 − 1/e)-competitive as k → ∞, for small bids
-- statement:
--   Consider the adwords problem with unit budgets, and the discrete tradeoff algorithm with $k$ slabs that assigns each arriving query to a bidder with remaining budget maximizing $\text{bid}\times\psi_k(\text{slab})$, where
--   $$\psi_k(i)=\sum_{j=i}^{k-1}y^*_j,\qquad y^*_j=\frac1k\Bigl(1-\frac1k\Bigr)^{k-j-1}.$$
--   For every $\delta>0$ there is $k_0$ such that for every $k\ge k_0$ there is $\eta>0$ with the following property. For every instance with $N$ bidders, $M$ queries and bids $0\le c_{b,t}\le\eta$, every run $\sigma$ of the algorithm (with any tie-breaking) and every offline allocation $\tau$,
--   $$\mathrm{rev}(\sigma)\ \ge\ \Bigl(1-\frac1e-\delta\Bigr)\,\mathrm{rev}(\tau),$$
--   where the revenue of an allocation counts each bidder's assigned bids up to its budget.
--
--   That is, the competitive ratio of the algorithm tends to $1-1/e$ as $k\to\infty$ when bids are small compared to budgets.
--
--   **Formalization Note**
--   1. "As $k$ tends to infinity" is quantified as $\forall\delta\,\exists k_0\,\forall k\ge k_0$, and "each bid is small compared to the corresponding budget" (§2) as the bound $\eta$, chosen after $k$ and independent of the instance.
--   2. $\psi_k$ is the defining sum; the closed form printed in the theorem, $1-(1-1/k)^{k-i+1}$, is off by one in the exponent (the sum equals $1-(1-1/k)^{k-i}$).
--   3. The comparator is every offline allocation. The paper's simplifying assumption that the offline optimum exhausts every budget is dropped, as §4 and §6 (item 2) say the proof extends without it. Budgets are kept equal to $1$.
--   4. Only the lower bound on the ratio is stated; the paper's proof gives only this direction.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 12, Theorem 8 (model: p. 5 §2, pp. 5–6 §3)

import Mathlib
import Definitions.Def_AdWordsMSVV_Tradeoff_Setting
import Definitions.Def_AdWordsMSVV_Tradeoff_LP

namespace AdWordsMSVV.Tradeoff
theorem theorem_8 :
    ∀ δ : ℝ, 0 < δ → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ η : ℝ, 0 < η ∧
      ∀ (N M : ℕ) (bid : Fin N → Fin M → ℝ), (∀ b t, 0 ≤ bid b t ∧ bid b t ≤ η) →
      ∀ σ : Fin M → Option (Fin N), IsRun (psi k) k bid σ →
      ∀ τ : Fin M → Option (Fin N),
        (1 - Real.exp (-1) - δ) * revenue bid τ ≤ revenue bid σ := by sorry
end AdWordsMSVV.Tradeoff
