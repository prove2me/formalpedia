-- Prove2me | Theorems.Thm_FenchelRobust_Counterpart_eq_13_15_duality
-- name    : FenchelRobust.Counterpart.eq_13_15_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T09:29:41.475356+00:00
-- url     : https://prove2.me/theorems/efd408b5-d58d-4180-a8d5-ca3593311643
-- title:
--   Eqs. (13)–(15) — attained Fenchel dual representation of worst-case value
-- statement:
--   Let $Z$ be nonempty, convex, and compact with $0\in\operatorname{ri}Z$. Let $f(\cdot,x)$ be concave on its effective domain $D(x)$ for every $x$, and assume $a^0\in\operatorname{ri}D(x)$ for every $x$. With $U=a^0+AZ$ and $F(x)=\sup_{a\in U\cap D(x)}f(a,x)$, for every decision $x$,
--   $$F(x)=\inf_{v\in\mathbb R^m}\bigl(\delta^*(v\mid U)-f_*(v,x)\bigr),$$
--   and some $v$ attains this infimum. This is the strong-duality identity immediately before the affine-support calculation in the proof of Theorem 2.
--
--   **Formalization Note.** The paper writes $\max$ and $\min$; the statement uses an extended-real supremum and infimum plus an explicit attaining vector. The function is represented only on its effective domain. Closedness from the general Notation paragraph is omitted: the relative-interior qualification supports the duality step without it.
-- source:
--   Ben-Tal, den Hertog, Vial, Deriving robust counterparts of nonlinear uncertain inequalities, CentER Discussion Paper 2012-053 (July 2, 2012), p. 5, Eqs. (13)–(15), proof of Theorem 2

import Mathlib
import Definitions.Def_FenchelRobust_Counterpart_Model

namespace FenchelRobust.Counterpart

/-- Equations (13)–(15), including the attainment indicated by `min`. -/
theorem eq_13_15_duality {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (hZnonempty : Z.Nonempty) (hZconvex : Convex ℝ Z) (hZcompact : IsCompact Z)
    (hZzero : (0 : Fin L → ℝ) ∈ intrinsicInterior ℝ Z)
    (hconcave : ∀ x, ConcaveOn ℝ (D x) (fun a => f a x))
    (hregular : Regular a0 D) :
    ∀ x : Fin n → ℝ,
      let F := worstCase a0 A Z D f x
      let dual := fun v : Fin m → ℝ =>
        supportFun (uncertaintySet a0 A Z) v - concaveConj (D x) (fun a => f a x) v
      F = (⨅ v, dual v) ∧ ∃ v, F = dual v := by sorry

end FenchelRobust.Counterpart
