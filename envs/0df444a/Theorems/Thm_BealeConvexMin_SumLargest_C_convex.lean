-- Prove2me | Theorems.Thm_BealeConvexMin_SumLargest_C_convex
-- name    : BealeConvexMin.SumLargest.C_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:38:20.902883+00:00
-- url     : https://prove2.me/theorems/ad160cac-c23f-4f11-b2ef-4a1c6e0ca8f7
-- title:
--   §4, p. 179 — $C$ = $A$ + sum of the $\tau$ largest of $L_0,\dots,L_s$ is convex
-- statement:
--   In the setting of Theorem 1 of Beale's paper, let $A$ and $L_0$ be affine functions of the variables $(z,u)$, let $L_f=L_0-u_f$ for $f=1,\dots,s$, and let $0\le\tau\le s+1$. Then
--   $$C(z,u)=A(z,u)+\bigl(\text{sum of the }\tau\text{ largest of }L_0(z,u),\dots,L_s(z,u)\bigr)$$
--   is a convex function of $(z,u)$ on the whole space.
--
--   Beale remarks that "$C$ can easily be shown to be convex, [but] it is not everywhere differentiable"; convexity is what turns the local optimality test of Theorem 1 into a global one.
--
--   **Formalization Note** The hypothesis $\tau\le s+1$ says that $\tau$ does not exceed the number of forms, as in the paper's "$t$ largest of $g$ forms"; outside it the Lean sum-of-largest is a junk $0$.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 179 (PDF p. 7), §4, the paragraph before Theorem 1

import Mathlib
import Definitions.Def_BealeConvexMin_SumLargest_sumLargest
import Definitions.Def_BealeConvexMin_SumLargest_Forms

namespace BealeConvexMin.SumLargest

/-- Beale (1955), §4, p. 179 (the paragraph before Theorem 1): "`C` can easily be shown to be
convex". Here `C = A + ` (sum of the `τ` largest of `L_0, …, L_s`), with `τ` at most the number
`s + 1` of forms, is convex as a function of all the variables `(z, u)`. -/
theorem C_convex {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ ≤ s + 1) :
    ConvexOn ℝ Set.univ (fun p : (Fin r → ℝ) × (Fin s → ℝ) => P.C τ p.1 p.2) := by sorry

end BealeConvexMin.SumLargest
