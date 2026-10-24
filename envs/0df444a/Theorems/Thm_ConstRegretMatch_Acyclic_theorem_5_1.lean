-- Prove2me | Theorems.Thm_ConstRegretMatch_Acyclic_theorem_5_1
-- name    : ConstRegretMatch.Acyclic.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:37:29.817204+00:00
-- url     : https://prove2.me/theorems/d073d01e-6124-49aa-8cb3-3ef7bc077b76
-- title:
--   Theorem 5.1, p. 25 — in (SPP)-acyclic networks the optimal solution of (SPP) is yˡλ with yˡ ∈ {−1, 0, 1}ⁿ, for every λ̃ > 0 with yˡλ̃ > 0
-- statement:
--   Let $(M, \lambda, r)$ be a matching network that satisfies the general position condition and is (SPP)-acyclic, and let $(z^*, s^*)$ be the unique non-degenerate optimal solution of (SPP), with $\mathcal M_+ = \{m : z^*_m > 0\}$ and $\mathcal Q_+ = \{j : s^*_j > 0\}$.
--
--   Then there exist vectors $y^l \in \{-1, 0, 1\}^n$, one for each $l \in \mathcal M_+ \cup \mathcal Q_+$, such that
--   $$z^*_m = y^m\lambda > 0 \ \text{ for all } m \in \mathcal M_+, \qquad s^*_j = y^j\lambda > 0 \ \text{ for all } j \in \mathcal Q_+,$$
--   and such that every right-hand side $\tilde\lambda > 0$ with $y^l\tilde\lambda > 0$ for all $l \in \mathcal M_+ \cup \mathcal Q_+$ induces the optimal solution $(z^*(\tilde\lambda), s^*(\tilde\lambda))$:
--   $$z^*_m(\tilde\lambda) = y^m\tilde\lambda\ (m \in \mathcal M_+),\quad z^*_m(\tilde\lambda) = 0\ (m \in \mathcal M_0),\quad s^*_j(\tilde\lambda) = y^j\tilde\lambda\ (j \in \mathcal Q_+),\quad s^*_j(\tilde\lambda) = 0\ (j \in \mathcal Q_0)$$
--   is the unique optimal solution of $\max\{r\cdot z : Mz + s = \tilde\lambda,\ z \ge 0,\ s \ge 0\}$.
--
--   Each basic variable of the optimal solution is thus a signed sum of arrival rates, so in (SPP)-acyclic networks the general position gap is a difference of sums of arrival probabilities.
--
--   **Formalization Note** The vectors are integer-valued and cast to $\mathbb R$ in the products $y^l\lambda = \sum_i y^l_i\lambda_i$. "Induces the optimal solution" is read as the unique optimal solution; $\tilde\lambda$ is any positive vector (it need not sum to one), and (SPP) at $\tilde\lambda$ uses the same $M$ and $r$. The second clause is what ties the vectors $y^l$ to the rows of the inverse of the optimal basis matrix; it is part of the statement.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 25, Theorem 5.1; proof App. C, pp. 44–46

import Mathlib
import Definitions.Def_ConstRegretMatch_Acyclic_Network
import Definitions.Def_ConstRegretMatch_Acyclic_SPP
import Definitions.Def_ConstRegretMatch_Acyclic_Residual

namespace ConstRegretMatch.Acyclic

/-- Theorem 5.1, p. 25 (explicit optimal solution of (SPP)): assume GP and (SPP)-acyclicity, with
`(z*, s*)` the unique non-degenerate optimal solution. Then there are vectors `yˡ ∈ {-1, 0, 1}ⁿ`, one
for each `l ∈ ℳ₊ ∪ 𝒬₊`, with `z*_m = yᵐλ > 0` for `m ∈ ℳ₊` and `s*_j = yʲλ > 0` for `j ∈ 𝒬₊`;
and every right-hand side `λ̃ > 0` with `yˡλ̃ > 0` for all `l ∈ ℳ₊ ∪ 𝒬₊` induces the optimal
solution `z̃_m = yᵐλ̃` (`m ∈ ℳ₊`), `z̃_m = 0` (`m ∈ ℳ₀`), `s̃_j = yʲλ̃` (`j ∈ 𝒬₊`), `s̃_j = 0`
(`j ∈ 𝒬₀`), which is the unique optimal solution of (SPP) with right-hand side `λ̃`. -/
theorem theorem_5_1 {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (hr : ConstRegretMatch.Upper.IsMatchValues r) (lam : Fin n → ℝ) (hlam : ConstRegretMatch.Upper.IsArrivalRates lam)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hGP : IsGP N r lam z s)
    (hacyc : IsSPPAcyclic N r lam z s) :
    ∃ y : ConstRegretMatch.Upper.BasisIdx z s → Fin n → ℤ,
      (∀ c i, y c i = -1 ∨ y c i = 0 ∨ y c i = 1) ∧
      (∀ c, ConstRegretMatch.Upper.basicPart z s c = ∑ i, (y c i : ℝ) * lam i ∧ 0 < ∑ i, (y c i : ℝ) * lam i) ∧
      ∀ lamt : Fin n → ℝ, (∀ i, 0 < lamt i) → (∀ c, 0 < ∑ i, (y c i : ℝ) * lamt i) →
        SPPUniqueOptimal N r lamt
          (basisSolZ (fun c => ∑ i, (y c i : ℝ) * lamt i))
          (basisSolS (fun c => ∑ i, (y c i : ℝ) * lamt i)) := by sorry

end ConstRegretMatch.Acyclic
