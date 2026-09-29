-- Prove2me | Theorems.Thm_BealeConvexMin_SumLargest_theorem1b
-- name    : BealeConvexMin.SumLargest.theorem1b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:40:06.688714+00:00
-- url     : https://prove2.me/theorems/4e6ac69c-9150-496d-a197-f0f1018fcd6b
-- title:
--   Theorem 1 (b), p. 180 — optimality conditions when $\tau=s+1$
-- statement:
--   Consider the setting of Theorem 1 (a) of Beale's paper, but with $\tau=s+1$, so that $C=A+L_0+L_1+\dots+L_s$. Let $F$ be the set of free $z_l$. Then
--   $$C\ \text{is minimized when all } z_l, u_f \text{ vanish}\iff (4.5)\ \text{holds and}\ \varphi_f+\tau\theta_f-1=0\ \text{for all } f .$$
--   Otherwise, for any $f$ with $\varphi_f+\tau\theta_f-1\neq0$, there is a value $v$ with the opposite sign to $\varphi_f+\tau\theta_f-1$ such that setting $u_f=v$ and all other variables to zero gives $C<C(0,0)$.
--
--   This is the boundary case excluded from Theorem 1 (a), in which every form is among the "$\tau$ largest" and the objective is affine.
--
--   **Formalization Note** "Minimized" is the global minimum over $\{z_l\ge0 \text{ for } l\notin F\}$, as in Theorem 1 (a). The paper's $f=1,\dots,s$ are Lean's $0,\dots,s-1$.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 180 (PDF p. 8), Theorem 1 (b)

import Mathlib
import Definitions.Def_BealeConvexMin_SumLargest_sumLargest
import Definitions.Def_BealeConvexMin_SumLargest_Forms

namespace BealeConvexMin.SumLargest

/-- Beale (1955), Theorem 1 (b), p. 180. In the setting of Theorem 1 (a) but with `τ = s + 1`
(so `C = A + L_0 + L_1 + ⋯ + L_s`), `C` is minimized when all the `z_l` and `u_f` vanish if and
only if (4.5) holds and in addition `φ_f + τθ_f − 1 = 0` for all `f`. Otherwise (for an `f` with
`φ_f + τθ_f − 1 ≠ 0`) `C` can be decreased by giving `u_f` some value with the opposite sign to
this quantity, the other variables staying at zero. `F` is the set of `l` with `z_l` free. -/
theorem theorem1b {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ = s + 1) (F : Finset (Fin r)) :
    (P.IsMinimizedAtZero τ F ↔
      P.Cond45 τ F ∧ ∀ f : Fin s, P.φ f + (τ : ℝ) * P.θ f - 1 = 0) ∧
    (∀ f : Fin s, P.φ f + (τ : ℝ) * P.θ f - 1 ≠ 0 →
      ∃ v : ℝ, v * (P.φ f + (τ : ℝ) * P.θ f - 1) < 0 ∧
        P.C τ 0 (Pi.single f v) < P.C τ 0 0) := by sorry

end BealeConvexMin.SumLargest
