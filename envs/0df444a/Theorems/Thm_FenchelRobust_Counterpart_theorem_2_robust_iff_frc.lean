-- Prove2me | Theorems.Thm_FenchelRobust_Counterpart_theorem_2_robust_iff_frc
-- name    : FenchelRobust.Counterpart.theorem_2_robust_iff_frc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:29:59.099528+00:00
-- url     : https://prove2.me/theorems/ed52341c-5fa7-4353-9452-9cf063917322
-- title:
--   Theorem 2 — robust feasibility if and only if the Fenchel counterpart is solvable
-- statement:
--   Let $a^0\in\mathbb R^m$, $A\in\mathbb R^{m\times L}$, and let $Z\subseteq\mathbb R^L$ be nonempty, convex, and compact with $0\in\operatorname{ri}Z$. Let $D(x)$ be the effective domain of $f(\cdot,x)$, suppose $f(\cdot,x)$ is concave on $D(x)$ for every $x$, and suppose $a^0\in\operatorname{ri}D(x)$ for every $x$. For $U=\{a^0+A\zeta:\zeta\in Z\}$ and every decision $x\in\mathbb R^n$,
--   $$\bigl[\,f(a,x)\le0\ \text{for all }a\in U\cap D(x)\,\bigr]\quad\Longleftrightarrow\quad\exists v\in\mathbb R^m:\ (a^0)^Tv+\delta^*(A^Tv\mid Z)-f_*(v,x)\le0.$$
--   Here $f_*(v,x)=\inf_{a\in D(x)}(a^Tv-f(a,x))$. The equivalence turns a constraint required for every uncertain parameter into one inequality with an auxiliary vector $v$.
--
--   **Formalization Note.** The paper writes $f=-\infty$ outside its effective domain and writes maxima and minima; the Lean representation restricts the domain explicitly and uses extended-real extrema. It retains relative interior, rather than ordinary interior. Closedness mentioned in the Notation paragraph is omitted because the duality argument needs proper concavity and the relative-interior qualification, not closedness.
-- source:
--   Ben-Tal, den Hertog, Vial, Deriving robust counterparts of nonlinear uncertain inequalities, CentER Discussion Paper 2012-053 (July 2, 2012), p. 4, Theorem 2 and Eq. (12); proof p. 5

import Mathlib
import Definitions.Def_FenchelRobust_Counterpart_Model

namespace FenchelRobust.Counterpart

/-- Theorem 2: robust feasibility is equivalent to solvability of (FRC). -/
theorem theorem_2_robust_iff_frc {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (hZnonempty : Z.Nonempty) (hZconvex : Convex ℝ Z) (hZcompact : IsCompact Z)
    (hZzero : (0 : Fin L → ℝ) ∈ intrinsicInterior ℝ Z)
    (hconcave : ∀ x, ConcaveOn ℝ (D x) (fun a => f a x))
    (hregular : Regular a0 D) :
    ∀ x : Fin n → ℝ,
      RobustFeasible a0 A Z D f x ↔
        ∃ v : Fin m → ℝ, frcValue a0 A Z D f x v ≤ 0 := by sorry

end FenchelRobust.Counterpart
