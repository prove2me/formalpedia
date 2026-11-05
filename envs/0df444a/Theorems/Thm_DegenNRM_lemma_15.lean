-- Prove2me | Theorems.Thm_DegenNRM_lemma_15
-- name    : DegenNRM.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:34:42.206199+00:00
-- url     : https://prove2.me/theorems/773a6acb-342f-4366-90ba-5e58155550ca
-- title:
--   Lemma 15 — Mangasarian–Shiau: solutions of $\hat Ax\le b$ are $\mu$-Lipschitz in $b$ (corrected: (43) consistent)
-- statement:
--   Let $\hat A$ be a real $\ell\times k$ matrix and let $\mu$ be the constant
--   $$\mu=\sup_v\Big\{\|v\|_1:\|v^\top\hat A\|_1=1,\ v\ge0,\ \text{the rows of }\hat A\text{ on the support of }v\text{ are linearly independent}\Big\}.$$
--   Then
--
--   1. the set in the supremum is bounded above, so $\mu<\infty$;
--   2. for all $b_1,b_2\in\mathbb R^\ell$ such that the system $\hat Ax\le b_2$ (43) has a solution, and every solution $x_1$ of $\hat Ax\le b_1$ (42), there is a solution $x_2$ of (43) with
--   $$\|x_1-x_2\|_\infty\le\mu\,\|b_1-b_2\|_\infty.$$
--
--   This is Theorem 2.2 of Mangasarian and Shiau (1987), *Lipschitz continuity of solutions of linear inequalities, programs and complementarity problems*, SIAM J. Control Optim. 25(3), 583–595. The paper uses it, through Claim 1, to prove Lemma 4.
--
--   Differences from the source:
--
--   - correction: for any solution x₁ of (42) there exists a solution x₂ of (43) with ‖x₁ − x₂‖∞ ≤ µ‖b₁ − b₂‖∞, with no hypothesis on (43) → the same conclusion when (43) has a solution; reason: false when (43) is infeasible: Â = (1, −1)ᵀ, b₁ = (0, 0), b₂ = (0, −1); x₁ = 0 solves (42) but (43) says x ≤ 0 and x ≥ 1. Mangasarian and Shiau assume consistency, and Lemma 4's proof only applies the lemma to consistent systems
--   - generalization: µ as defined (its finiteness is asserted on p.43: 'we know that µ in (69) is finite') → the conclusion also asserts that the set in the supremum is bounded above; reason: dropping the first conjunct gives the printed statement
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, Lemma 15, p.36; proof of Lemma 4, p.43

import Mathlib
import Definitions.Def_DegenNRM_msMu

namespace DegenNRM

/-- **Lemma 15, corrected (Theorem 2.2 of Mangasarian and Shiau 1987)** (Jiang, Ma & Zhang,
arXiv:2210.07996v5, Lemma 15, p.36).

Let `Â` be a real `ℓ × k` matrix and consider the linear systems `Âx ≤ b₁` (42) and
`Âx ≤ b₂` (43). The constant `µ` (`msMu`) is finite, and if (43) has a solution, then for any
solution `x₁` of (42) there is a solution `x₂` of (43) with `‖x₁ - x₂‖_∞ ≤ µ ‖b₁ - b₂‖_∞`.

**Formalization Note.** The printed lemma has no hypothesis on (43); it is false when (43) is
infeasible (`Â = (1, -1)ᵀ`, `b₁ = (0, 0)`, `b₂ = (0, -1)`: `x₁ = 0` solves (42) but (43) says
`x ≤ 0` and `x ≥ 1`). Consistency of (43) is added, as in Mangasarian and Shiau's theorem.
Finiteness of `µ` ("µ in (69) is finite", p.43) is the first conjunct. `‖·‖_∞` is the sup norm
of `Fin k → ℝ` and `Fin ℓ → ℝ`. -/
theorem lemma_15 {ℓ k : ℕ} (A : Matrix (Fin ℓ) (Fin k) ℝ) :
    BddAbove {μ | ∃ v : Fin ℓ → ℝ, μ = ∑ i, |v i| ∧ (∑ j, |∑ i, v i * A i j|) = 1 ∧ 0 ≤ v ∧
      LinearIndependent ℝ (fun i : {i : Fin ℓ // v i ≠ 0} => A i.1)} ∧
    ∀ b₁ b₂ : Fin ℓ → ℝ, (∃ x : Fin k → ℝ, A.mulVec x ≤ b₂) →
      ∀ x₁ : Fin k → ℝ, A.mulVec x₁ ≤ b₁ →
        ∃ x₂ : Fin k → ℝ, A.mulVec x₂ ≤ b₂ ∧ ‖x₁ - x₂‖ ≤ msMu A * ‖b₁ - b₂‖ := by sorry

end DegenNRM
