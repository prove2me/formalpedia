-- Prove2me | Theorems.Thm_ChitourPrescribedTime_Linear_proposition11_lmi
-- name    : ChitourPrescribedTime.Linear.proposition11_lmi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:01:02.275227+00:00
-- url     : https://prove2.me/theorems/31240f47-95e2-45d1-9c10-33f5dce2d957
-- title:
--   Proposition 11 — the LMI survives the perturbation $a D_{\mathbf r}$ for $|a|\le C_0$
-- statement:
--   Let $n\ge 1$ and $\underline b>0$. Then there exist constants $\rho_0>0$ and $C_0>0$, a real symmetric positive definite $n\times n$ matrix $S$, and a vector $K\in\mathbb R^n$ such that
--   $$\big(a D_{\mathbf r} + J_n - b\, e_n K^T\big)^T S + S\big(a D_{\mathbf r} + J_n - b\, e_n K^T\big) \preceq -\rho_0\, \mathrm{Id}_n$$
--   for every $a\in[-C_0,C_0]$ and every $b\ge\underline b$. Here $D_{\mathbf r}=\operatorname{diag}(n,n-1,\dots,1)$ and $\preceq$ is the Loewner order.
--
--   This is the form of the LMI used for the transformed dynamics (13), where the extra term $a(s)D_{\mathbf r}$ comes from the time-varying dilation.
--
--   **Formalization Note** `≤` on matrices is the Loewner order (`open scoped MatrixOrder`), and `S.PosDef` includes symmetry. The hypothesis $n\ge1$ is the standing assumption of §3.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1028, Proposition 11, eq. (16)

import Mathlib
import Definitions.Def_ChitourPrescribedTime_Linear_chain

namespace ChitourPrescribedTime.Linear

open Matrix
open scoped MatrixOrder

/-- Proposition 11 (p. 1028): for `n ≥ 1` and `b̲ > 0` there are `ρ₀, C₀ > 0`, a real symmetric
positive definite `S` and `K ∈ ℝ^n` with
`(a D_r + J_n - b e_n Kᵀ)ᵀ S + S (a D_r + J_n - b e_n Kᵀ) ≤ -ρ₀ Id_n` (Loewner order) for every
`a ∈ [-C₀, C₀]` and every `b ≥ b̲`. -/
theorem proposition11_lmi (n : ℕ) (hn : 1 ≤ n) (bmin : ℝ) (hbmin : 0 < bmin) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∃ C0 : ℝ, 0 < C0 ∧ ∃ S : Matrix (Fin n) (Fin n) ℝ, S.PosDef ∧
      ∃ K : Fin n → ℝ, ∀ a : ℝ, a ∈ Set.Icc (-C0) C0 → ∀ b : ℝ, bmin ≤ b →
        (a • Dr n + jordanBlock n - b • vecMulVec (eN n) K)ᵀ * S +
            S * (a • Dr n + jordanBlock n - b • vecMulVec (eN n) K)
          ≤ -(ρ0 • (1 : Matrix (Fin n) (Fin n) ℝ)) := by sorry

end ChitourPrescribedTime.Linear
