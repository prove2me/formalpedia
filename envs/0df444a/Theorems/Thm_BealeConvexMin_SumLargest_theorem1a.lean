-- Prove2me | Theorems.Thm_BealeConvexMin_SumLargest_theorem1a
-- name    : BealeConvexMin.SumLargest.theorem1a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:40:37.200269+00:00
-- url     : https://prove2.me/theorems/60fe2604-3886-4e19-8f31-c926b1b0d8e0
-- title:
--   Theorem 1 (a), p. 179 — $C$ is minimized at the origin iff (4.5)
-- statement:
--   Let $z_l$ (for $l$ in a finite index set) and $u_1,\dots,u_s$ be real variables, and let
--   $$A=A_0+\sum_l A_l z_l+\sum_{f=1}^{s}\varphi_f u_f,\qquad L_0=c_{00}+\sum_l c_{0l} z_l+\sum_{f=1}^{s}\theta_f u_f,\qquad L_f=L_0-u_f\ (f=1,\dots,s).$$
--   Let $\tau\le s$ be a non-negative integer and let $C$ be $A$ plus the sum of the $\tau$ largest of $L_0,L_1,\dots,L_s$. Suppose all the $u_f$ and the $z_l$ with $l\in F$ are free variables, and the other $z_l$ are restricted to non-negative values. Then $C$ is minimized (over this feasible region) when all the $z_l$ and $u_f$ vanish if and only if
--   $$\begin{aligned}
--   &A_l+\tau c_{0l}\ge0\ \text{for all } l,\\
--   &A_l+\tau c_{0l}=0\ \text{for all } l\in F,\\
--   &0\le\varphi_f+\tau\theta_f\le1\ \text{for all } f,\\
--   &\tau-1\le\sum_{f=1}^{s}(\varphi_f+\tau\theta_f)\le\tau .
--   \end{aligned}\tag{4.5}$$
--
--   The objective is convex but not differentiable at the origin, where all $s+1$ forms coincide; (4.5) is the exact optimality test that replaces "all reduced costs are non-negative" in Beale's simplex-type method for minimizing the sum of the $t$ largest of a set of linear forms.
--
--   **Formalization Note** "Minimized" is the global statement $C(0,0)\le C(z,u)$ for every $(z,u)$ with $z_l\ge0$ for $l\notin F$. The index set of the $z_l$ is `Fin r` (possibly empty) and $F$ is a `Finset (Fin r)`. The paper's $f=1,\dots,s$ are Lean's $0,\dots,s-1$. The cases $\tau=0$ and $s=0$ are allowed, as on the page.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 179 (PDF p. 7), Theorem 1 (a), first half, conditions (4.5)

import Mathlib
import Definitions.Def_BealeConvexMin_SumLargest_sumLargest
import Definitions.Def_BealeConvexMin_SumLargest_Forms

namespace BealeConvexMin.SumLargest

/-- Beale (1955), Theorem 1 (a), p. 179, first half. Let `A = A_0 + Σ_l A_l z_l + Σ_{f=1}^{s} φ_f u_f`,
`L_0 = c_00 + Σ_l c_0l z_l + Σ_{f=1}^{s} θ_f u_f`, `L_f = L_0 − u_f` (`f = 1, …, s`), and let `C` be
`A` plus the sum of the `τ` largest of `L_0, L_1, …, L_s`, where `τ ≤ s`. If all the `u_f` and the
`z_l` with `l ∈ F` are free and the other `z_l` are restricted to non-negative values, then `C` is
minimized when all the `z_l` and `u_f` vanish if and only if (4.5) holds. -/
theorem theorem1a {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ ≤ s) (F : Finset (Fin r)) :
    P.IsMinimizedAtZero τ F ↔ P.Cond45 τ F := by sorry

end BealeConvexMin.SumLargest
