-- Prove2me | Theorems.Thm_ComonoNetPricing_DebtEquity_corollary_A_4
-- name    : ComonoNetPricing.DebtEquity.corollary_A_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:33.645683+00:00
-- url     : https://prove2.me/theorems/f873f0bd-8bae-4dc6-9d9c-4eb0bb3a6559
-- title:
--   Corollary A.4, p. 35 — the fictitious default algorithm (closed form of (iv)) terminates at the greatest clearing wealth
-- statement:
--   For a positive integer $n$, consider the Rogers–Veraart network under the standing assumptions and endowments $x \in \mathbb R^n_+$. Run the fictitious default algorithm: $V^{(0)} = x + \Pi^\top\bar p - \bar p$, $z^{(0)} = 0$, and for $k\ge1$, $z^{(k)} = \mathbb I_{\{V^{(k-1)}<0\}}$, $\Lambda = \operatorname{diag}(z^{(k)})$,
--   $$V^{(k)} = \big(I - (I - (1-\alpha_L)\Lambda)\,\Pi^\top\Lambda\big)^{-1}\big[(I - (1-\alpha_x)\Lambda)x + (I - (1-\alpha_L)\Lambda)\Pi^\top\bar p - \bar p\big].$$
--   Then
--
--   1. for every $z \in \{0,1\}^n$ the matrix $I - (I - (1-\alpha_L)\operatorname{diag}(z))\,\Pi^\top\operatorname{diag}(z)$ is nonsingular;
--   2. the algorithm terminates: there is a first index $k$ with $z^{(k+1)} = z^{(k)}$, and at that index $V^{(k)} = V(x)$, the greatest clearing wealth.
--
--   This is how the greatest clearing solution is computed, and it is the source of the piecewise linear formula for $V$ in §3.1.
--
--   **Formalization Note** The printed step (iv) gives two expressions; the first drops $\alpha_L$ before $\Pi^\top\Lambda V^{(k)}$ in the default bracket, which is a typo. The algorithm is stated with the second (closed-form) expression. Nonsingularity is stated in the proof of the corollary. The termination step is "if $z^{(k)} = z^{(k-1)}$ then $V^\uparrow = V^{(k-1)}$", here with $k$ shifted by one. No bound on the number of iterations is claimed, as on the page.
-- source:
--   Banerjee & Feinstein, Pricing of debt and equity in a financial network with comonotonic endowments, arXiv:1810.01372v5, p. 35, Corollary A.4 and its proof

import Mathlib
import Definitions.Def_ComonoNetPricing_DebtEquity_Network
import Definitions.Def_ComonoNetPricing_DebtEquity_Model

namespace ComonoNetPricing.DebtEquity

open Matrix

/-- Corollary A.4, p. 35 (fictitious default algorithm, closed form of step (iv)): under the
standing assumptions and for endowments `x ≥ 0`, (a) the matrix
`I − (I − (1 − α_L)Λ) Π⊤ Λ` is nonsingular for every default set `Λ = diag(z)` (stated in the
proof), and (b) the algorithm terminates: there is a first step `k` with `z^{(k+1)} = z^{(k)}`,
and then `V^{(k)}` is the greatest clearing wealth `V(x)`. The first line of the printed (iv)
drops `α_L` before `Π⊤ΛV^{(k)}` in the default bracket; the closed form (second line) is used. -/
theorem corollary_A_4 {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing) (x : Fin n → ℝ) (hx : 0 ≤ x) :
    (∀ S : Finset (Fin n), IsUnit (N.Mmat S).det) ∧
      ∃ k : ℕ, N.fdaZ x (k + 1) = N.fdaZ x k ∧ (∀ j < k, N.fdaZ x (j + 1) ≠ N.fdaZ x j) ∧
        N.fdaV x k = N.clearingWealth x := by sorry

end ComonoNetPricing.DebtEquity
