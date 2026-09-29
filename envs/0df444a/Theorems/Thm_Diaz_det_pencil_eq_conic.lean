-- Prove2me | Theorems.Thm_Diaz_det_pencil_eq_conic
-- name    : Diaz.det_pencil_eq_conic
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:45.796792+00:00
-- url     : https://prove2.me/theorems/f93dad25-84e2-4727-8b3a-cf2dd8103815
-- title:
--   Determinantal descent in dimension two: the pencil determinant is a multiple of $x_1x_2-\rho x_0^2$
-- statement:
--   **Determinantal descent in dimension two: a singular pencil over the candidate's hull descends to the
--   Diaz conic.**
--
--   Let $K \subseteq \mathbb{C}$ be a subfield, $u \neq 0$ transcendental over $K$ with $\rho = u\bar u \in K$,
--   and let $A, B, C$ be $2\times2$ matrices with entries in $K$. If
--
--   $$\det\bigl(A + uB + \bar u\,C\bigr) = 0,$$
--
--   then there is $c \in K$ such that for all $x, y, z \in \mathbb{C}$
--
--   $$\det\bigl(xA + yB + zC\bigr) = c\,\bigl(yz - \rho\,x^{2}\bigr).$$
--
--   **Why.** Polarizing the $2\times2$ determinant writes $\det(xA+yB+zC)$ as a ternary quadratic form with
--   six coefficients in $K$. Substituting $\bar u = \rho/u$ into the hypothesis and clearing $u^2$ turns it
--   into the vanishing of a polynomial of degree four in $u$ with coefficients in $K$; transcendence of $u$
--   kills all five of its coefficients. What survives is $\det B = 0$, $\det C = 0$, the vanishing of the
--   $xy$- and $xz$-coefficients, and $\det A + \rho\,\beta = 0$ where $\beta$ is the $yz$-coefficient. The
--   displayed identity is then exactly what is left, with $c = \beta$.
--
--   **Role.** This is Theorem 4.2 (*Uniqueness of the obstruction*) of the note cited below, and the $2\times2$
--   case of a determinantal descent to the Diaz conic for minors of any size (Carlo Perassi's, unpublished). It says that a
--   singular matrix over the candidate's hull $W_u = \overline{\mathbb{Q}} \oplus \overline{\mathbb{Q}}u
--   \oplus \overline{\mathbb{Q}}\bar u$ cannot be singular by accident: its determinant form, as a form in
--   the three hull coordinates, is forced to be a scalar multiple of $\mathcal{Q}_\rho = x_1x_2 - \rho x_0^2$
--   — the conic on which the candidate lives. Two special cases are worth reading off: taking $x = z = 0$
--   gives $\det B = 0$, taking $x = y = 0$ gives $\det C = 0$; and $c = 0$ is exactly the degenerate branch
--   in which the whole pencil is singular, which by the Dasgupta--Kakde alternative is the branch with a
--   vanishing algebraic matrix coefficient.
--
--   Note that the statement is unconditional given the transcendence hypothesis — no unproved transcendence
--   conjecture enters — because $\bar u = \rho/u$ makes the candidate's hull a rational function field in one
--   transcendental.
--
--   Source: Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Section 4 (*The precise open
--   boundary*), Theorem 4.2 (*Uniqueness of the obstruction*). No novelty is claimed.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Theorem 4.2. Formal proof: Diaz modulus mission, 8 September 2026 (C. Perassi).

import Mathlib

open ComplexConjugate

theorem Diaz.det_pencil_eq_conic {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u) (hu0 : u ≠ 0)
    (hρ : u * conj u ∈ K) (A B C : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ i j, A i j ∈ K) (hB : ∀ i j, B i j ∈ K) (hC : ∀ i j, C i j ∈ K)
    (hdet : (A + u • B + (conj u) • C).det = 0) :
    ∃ c : ℂ, c ∈ K ∧ ∀ x y z : ℂ,
      (x • A + y • B + z • C).det = c * (y * z - (u * conj u) * x ^ 2) := by sorry
