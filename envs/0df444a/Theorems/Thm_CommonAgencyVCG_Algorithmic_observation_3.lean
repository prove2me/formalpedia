-- Prove2me | Theorems.Thm_CommonAgencyVCG_Algorithmic_observation_3
-- name    : CommonAgencyVCG.Algorithmic.observation_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:32.395561+00:00
-- url     : https://prove2.me/theorems/2dcfbfb3-faf6-4cdb-ba78-536ded0c0677
-- title:
--   Observation 3, p. 19 — under k_{a*(b)} ≤ Σ m^ℓ(b), LP3's optimal solutions are exactly the x of Claim 3 (2)
-- statement:
--   Fix a common agency setting satisfying the standing assumptions and a bid profile $b\in\mathcal V$ with $k_{a^*(b)} \le \sum_\ell m^\ell(b)$. Consider the linear program
--   $$\max_{x^b\in\mathbb R^n} \sum_{\ell\in[n]} x^b_\ell \quad\text{s.t.}\quad \sum_{\ell\in[n]} x^b_\ell \le 1,\quad x^b_\ell\, k_{a^*(b)} \le m^\ell(b),\quad 0\le x^b_\ell\ \ \forall\ell. \tag{LP3}$$
--   Then:
--
--   1. there is $x^b$ with $0\le x^b_\ell$, $x^b_\ell\,k_{a^*(b)}\le m^\ell(b)$ for all $\ell$ and $\sum_\ell x^b_\ell = 1$;
--   2. a vector is an optimal solution of LP3 if and only if it satisfies the conditions of item 1.
--
--   So LP3 computes the weights $x^b$ required in Claim 3 (2) (line 6 of Algorithm 1).
--
--   **Formalization Note** The observation's polynomial-time claim is not formalized; the mathematical content, that LP3's optima are exactly the weights of Claim 3 (2) and that one exists, is stated.
-- source:
--   Alon, Lavi, Shamash, Talgam-Cohen, Incomplete Information VCG Contracts for Common Agency, arXiv:2105.14998v1, p. 19, Observation 3 (LP3)

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1

namespace CommonAgencyVCG.Algorithmic

variable {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]

/-- Observation 3, p. 19 (mathematical content): when `k_{a*(b)} ≤ ∑_ℓ m^ℓ(b)`, LP3 —
maximize `∑_ℓ x_ℓ` subject to `∑_ℓ x_ℓ ≤ 1`, `x_ℓ k_{a*(b)} ≤ m^ℓ(b)`, `0 ≤ x_ℓ` — has a feasible
point with `∑_ℓ x_ℓ = 1`, and its optimal solutions are exactly the `x` of Claim 3 (2). -/
theorem observation_3 (S : Setting n A O) (hS : S.Standing) (b : Fin n → O → ℝ) (hb : InDom S b)
    (hk : kCost S (aStar S b) ≤ ∑ ℓ, mBound S ℓ b) :
    (∃ x : Fin n → ℝ, (∀ ℓ, 0 ≤ x ℓ ∧ x ℓ * kCost S (aStar S b) ≤ mBound S ℓ b) ∧ ∑ ℓ, x ℓ = 1) ∧
      ∀ x : Fin n → ℝ,
        (((∑ ℓ, x ℓ ≤ 1) ∧ ∀ ℓ, 0 ≤ x ℓ ∧ x ℓ * kCost S (aStar S b) ≤ mBound S ℓ b) ∧
            ∀ y : Fin n → ℝ, ((∑ ℓ, y ℓ ≤ 1) ∧
                ∀ ℓ, 0 ≤ y ℓ ∧ y ℓ * kCost S (aStar S b) ≤ mBound S ℓ b) →
              ∑ ℓ, y ℓ ≤ ∑ ℓ, x ℓ) ↔
          ((∀ ℓ, 0 ≤ x ℓ ∧ x ℓ * kCost S (aStar S b) ≤ mBound S ℓ b) ∧ ∑ ℓ, x ℓ = 1) := by sorry

end CommonAgencyVCG.Algorithmic
