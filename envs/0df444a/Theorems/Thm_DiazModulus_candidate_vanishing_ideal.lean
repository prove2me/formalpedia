-- Prove2me | Theorems.Thm_DiazModulus_candidate_vanishing_ideal
-- name    : DiazModulus.candidate_vanishing_ideal
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-12T14:11:28.739863+00:00
-- url     : https://prove2.me/theorems/e2d835da-4612-4134-bf11-eca300feeca9
-- title:
--   A Diaz candidate lies on no algebraic curve but its circle
-- statement:
--   Let $u=x+iy\in\mathbb{C}$ be a **candidate** for Diaz's modulus conjecture: $u\neq 0$, $|u|$ algebraic over $\mathbb{Q}$, and $e^{u}$ algebraic over $\mathbb{Q}$. Write $\rho=|u|^{2}\in\overline{\mathbb{Q}}$, and assume Hermite--Lindemann. Then for every polynomial $P\in \overline{\mathbb{Q}}[X,Y]$,
--
--   $$
--   P(x,y)=0 \quad\text{if and only if}\quad X^{2}+Y^{2}-\rho \text{ divides } P.
--   $$
--
--   In other words a candidate is algebraically generic on its own circle: it lies on no plane algebraic curve that does not contain the whole circle $x^{2}+y^{2}=\rho$ as a component.
--
--   The reverse direction is evaluation. For the forward direction, view $P$ as a polynomial in the real coordinate over $\overline{\mathbb{Q}}[Y]$, divide by the monic quadratic $X^{2}+(Y^{2}-\rho)$, and obtain a linear remainder $A(y)\,x+B(y)$. Vanishing at the point forces $A(y)x+B(y)=0$. Squaring and using $x^{2}=\rho-y^{2}$ yields a polynomial relation in the imaginary part; transcendence of $y$ over $\overline{\mathbb{Q}}$ makes that relation identically zero, so $A^{2}(\rho-Y^{2})=B^{2}$. The polynomial $\rho-Y^{2}$ is not a square in $\overline{\mathbb{Q}}[Y]$ when $\rho\neq 0$, hence $A=B=0$ and the quadratic divides $P$.
--
--   **Formalization Note.** The hypothesis `HermiteLindemann` is the mission's explicit `Prop`. Coordinates are `((u.re : ℝ) : ℂ)` and `((u.im : ℝ) : ℂ)`. Coefficients are the subtype `↥Qbar`.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Proposition 6.14. Background: G. Diaz, Utilisation de la conjugaison complexe dans l'etude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Theor. Nombres Bordeaux 16 (2004), 535-553, section 5.1. A hypothetical counterexample is algebraically generic on its own circle: every algebraic plane curve through it contains that whole circle.

import Definitions.Def_DiazModulus
open Complex

namespace DiazModulus
theorem candidate_vanishing_ideal (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u)
    (P : MvPolynomial (Fin 2) (↥Qbar)) :
    MvPolynomial.aeval
        (fun i : Fin 2 => if i = 0 then ((u.re : ℝ) : ℂ) else ((u.im : ℝ) : ℂ)) P = 0 ↔
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 -
          MvPolynomial.C ⟨((‖u‖ : ℝ) : ℂ) ^ 2,
            Subfield.pow_mem (s := Qbar) (mem_Qbar_iff.mpr h.2.1) 2⟩) ∣ P := by sorry
end DiazModulus
