-- Prove2me | Theorems.Thm_ChitourPrescribedTime_Linear_proposition10_lmi
-- name    : ChitourPrescribedTime.Linear.proposition10_lmi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:00:06.210988+00:00
-- url     : https://prove2.me/theorems/65a35d01-2e3f-4564-bce7-554be683412a
-- title:
--   Proposition 10 — an LMI for $J_n - b e_n K^T$ that holds for every $b \ge \underline b$
-- statement:
--   Let $n\ge 1$ and $\underline b>0$. Then there exist a constant $\rho>0$, a real symmetric positive definite $n\times n$ matrix $S$, and a vector $K\in\mathbb R^n$ such that
--   $$\big(J_n - b\, e_n K^T\big)^T S + S\big(J_n - b\, e_n K^T\big) \preceq -\rho\, \mathrm{Id}_n \qquad \text{for every } b\ge\underline b,$$
--   where $\preceq$ is the Loewner order on symmetric matrices ($A\preceq B$ iff $B-A$ is positive semidefinite).
--
--   The quantifiers matter: one Lyapunov matrix $S$ and one gain $K$ work for the whole unbounded range $b\in[\underline b,\infty)$ of control gains. Earlier results needed an upper bound $b\le\bar b$. This LMI is the basis of all the stability estimates of the linear feedback.
--
--   **Formalization Note** $e_n K^T$ is `vecMulVec (eN n) K`, `S.PosDef` includes symmetry, and `≤` on matrices is the Loewner order (`open scoped MatrixOrder`). The paper writes "$n\in\mathbb N$". The hypothesis $n\ge 1$ comes from the standing assumption of §3 ("Let $n$ be a positive integer"); for $n=0$ the statement is about empty matrices and trivially true.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1028, Proposition 10, eq. (15); proof in Appendix 6.1, pp. 1043–1044

import Mathlib
import Definitions.Def_ChitourPrescribedTime_Linear_chain

namespace ChitourPrescribedTime.Linear

open Matrix
open scoped MatrixOrder

/-- Proposition 10 (p. 1028): for `n ≥ 1` and `b̲ > 0` there are `ρ > 0`, a real symmetric positive
definite `S` and `K ∈ ℝ^n` with
`(J_n - b e_n Kᵀ)ᵀ S + S (J_n - b e_n Kᵀ) ≤ -ρ Id_n` (Loewner order) for **every** `b ≥ b̲`. -/
theorem proposition10_lmi (n : ℕ) (hn : 1 ≤ n) (bmin : ℝ) (hbmin : 0 < bmin) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ S : Matrix (Fin n) (Fin n) ℝ, S.PosDef ∧ ∃ K : Fin n → ℝ,
      ∀ b : ℝ, bmin ≤ b →
        (jordanBlock n - b • vecMulVec (eN n) K)ᵀ * S + S * (jordanBlock n - b • vecMulVec (eN n) K)
          ≤ -(ρ • (1 : Matrix (Fin n) (Fin n) ℝ)) := by sorry

end ChitourPrescribedTime.Linear
