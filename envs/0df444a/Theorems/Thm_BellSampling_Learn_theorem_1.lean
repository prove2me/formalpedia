-- Prove2me | Theorems.Thm_BellSampling_Learn_theorem_1
-- name    : BellSampling.Learn.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:46.323362+00:00
-- url     : https://prove2.me/theorems/26c0c2a1-4857-4e23-be3e-36c70007fcbd
-- title:
--   Theorem 1, p. 1 (explicit form, p. 2) — Algorithm 1 identifies an n-qubit stabilizer state from 2n+1 Bell samples except with probability at most 2⁻ⁿ
-- statement:
--   Let $\psi$ be an unknown $n$-qubit stabilizer state with stabilizer set $T=T(\psi)\subseteq\mathbb F_2^{2n}$. Run Algorithm 1: take $2n+1$ independent Bell samples $r_0,r_1,\dots,r_{2n}$, each on two fresh copies of $\psi$, and form the span of $r_1\oplus r_0,\dots,r_{2n}\oplus r_0$. Then:
--   1. **Steps 2–4 succeed with probability at least $1-2^{-n}$:**
--   $$\Pr\bigl[\operatorname{span}\{r_i\oplus r_0: 1\le i\le 2n\}=T\bigr]\ \ge\ 1-2^{-n},$$
--   where the probability is over the independent outcomes, each with the Bell-sampling law $p_\psi$.
--   2. **Step 5 identifies $\psi$:** for every basis $b_1,\dots,b_n$ of $T$ (any $n$ linearly independent elements of $T$) with corresponding Hermitian Pauli matrices $M_j$, each $M_j|\psi\rangle=\pm|\psi\rangle$, and every vector $\varphi$ that has the same eigenvalue as $\psi$ under every $M_j$ is a scalar multiple of $\psi$.
--
--   On the success event of part 1 every basis of the span found in step 4 is such a basis, so Algorithm 1 identifies $\psi$ except with probability at most $2^{-n}$, using $5n+2$ copies of $\psi$ and measuring at most two copies at a time. This is the explicit form of Theorem 1 ("$O(n)$ copies, fails with probability exponentially small in $n$").
--
--   **Formalization Note** The page states the failure probability, at most $2^{-n}$; the success form $\ge 1-2^{-n}$ is equivalent because the outcome probabilities sum to $1$, and it cannot be met by a degenerate outcome law. The copy count $5n+2$ and "at most two copies at a time" are properties of the model (one Bell sample per two fresh copies, one copy per sign measurement) and are not stated as separate clauses. The running time $O(n^3)$ is not formalized.
-- source:
--   Montanaro, Learning stabilizer states by Bell sampling, arXiv:1707.04012v2, p. 1, Theorem 1; p. 2, Algorithm 1 and the failure analysis

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace BellSampling.Learn
theorem theorem_1 (n : ℕ) (ψ : QState n) (hψ : IsStabilizerState ψ) :
    1 - 1 / (2 : ℝ) ^ n ≤ algo1Prob ψ (algo1Success ψ) ∧
    ∀ b : Fin n → PStr n, (∀ j, b j ∈ stabSet ψ) → LinearIndependent (ZMod 2) b →
      (∀ j, (pauliH (b j)).mulVec ψ = ψ ∨ (pauliH (b j)).mulVec ψ = -ψ) ∧
      ∀ φ : QState n,
        (∀ j (e : ℂ), (pauliH (b j)).mulVec ψ = e • ψ → (pauliH (b j)).mulVec φ = e • φ) →
        ∃ c : ℂ, φ = c • ψ := by sorry
end BellSampling.Learn
