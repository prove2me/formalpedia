-- Prove2me | Theorems.Thm_BoxTDIMinMax_Separable_proposition_2_8
-- name    : BoxTDIMinMax.Separable.proposition_2_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:27.362423+00:00
-- url     : https://prove2.me/theorems/d2bf3ec9-ddf2-421d-9183-4bb7bf381a04
-- title:
--   Proposition 2.8, p. 9 — adding a superfluous inequality qx ≥ β preserves TDI and box-TDI
-- statement:
--   Let $A\in\mathbb Q^{I\times S}$, $b\in\mathbb Q^I$, $R=\{x\in\mathbb R^S:Ax\ge b\}$, and let $q\in\mathbb Q^S$, $\beta\in\mathbb Q$ be such that the inequality $qx\ge\beta$ is **superfluous**: every $x\in R$ satisfies $qx\ge\beta$. Then:
--   1. if $Ax\ge b$ is TDI, then $[Ax\ge b,\ qx\ge\beta]$ is TDI;
--   2. if $Ax\ge b$ is box-TDI, then $[Ax\ge b,\ qx\ge\beta]$ is box-TDI.
--
--   Used in the proof of Proposition 2.9, where the bounds with infinite entries are reduced to finite ones.
--
--   **Formalization Note** Stated for a rational system $A$, $b$ (TDI is defined for rational systems, and the proof of Proposition 2.9 applies this to the rational system $[Qx\ge p,\ f_0\le x\le g_0]$); the integral case of the section's standing assumption is a special case. The new row is indexed by `Unit`.
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, p. 9, Proposition 2.8

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable

open Matrix

/-- Proposition 2.8, p. 9: adding to a TDI (resp. box-TDI) rational system `A x ≥ b` an inequality
`q x ≥ β` that every real point of `R = {x : A x ≥ b}` satisfies yields a TDI (resp. box-TDI)
system `[A x ≥ b, q x ≥ β]` (rows `ι ⊕ Unit`). -/
theorem proposition_2_8 {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (A : Matrix ι S ℚ) (b : ι → ℚ) (q : S → ℚ) (β : ℚ)
    (hsup : ∀ x ∈ realPts A b, (β : ℝ) ≤ ∑ s, (q s : ℝ) * x s) :
    (IsTDI A b →
        IsTDI (Matrix.fromRows A (Matrix.of fun (_ : Unit) s => q s)) (Sum.elim b fun _ => β)) ∧
      (IsBoxTDI A b →
        IsBoxTDI (Matrix.fromRows A (Matrix.of fun (_ : Unit) s => q s))
          (Sum.elim b fun _ => β)) := by sorry

end BoxTDIMinMax.Separable
