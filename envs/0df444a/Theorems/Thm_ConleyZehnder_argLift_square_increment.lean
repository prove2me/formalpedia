-- Prove2me | Theorems.Thm_ConleyZehnder_argLift_square_increment
-- name    : ConleyZehnder.argLift_square_increment
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T21:23:21.42299+00:00
-- url     : https://prove2.me/theorems/3a8f07cc-f757-4e5c-9e96-2c79c49d2b73
-- title:
--   The change of argument of a circle-valued map around the boundary of a square vanishes
-- statement:
--   Let $F:[0,1]\times[0,1]\to\mathbb C$ be continuous with $|F|=1$ everywhere. For a continuous $f:[0,1]\to S^1$, a continuous argument of $f$ is a continuous $\theta:[0,1]\to\mathbb R$ with $f(t)=e^{i\theta(t)}$, and its increment is $\theta(1)-\theta(0)$.
--
--   Let $a,b,c,d$ be continuous arguments of the four edge paths $t\mapsto F(0,t)$ (left), $s\mapsto F(s,1)$ (top), $s\mapsto F(s,0)$ (bottom) and $t\mapsto F(1,t)$ (right). Then
--   $$\bigl(a(1)-a(0)\bigr)+\bigl(b(1)-b(0)\bigr)=\bigl(c(1)-c(0)\bigr)+\bigl(d(1)-d(0)\bigr),$$
--   i.e. the total change of argument around the boundary of the square vanishes.
--
--   This is the basic invariance statement for winding numbers of maps from a square to the circle; it is used to compare degrees of $\hat\rho^2$ along families of symplectic paths whose endpoints move, as needed for the homotopy and naturality properties of the Conley–Zehnder index.
--
--   Formalization note: `IsArgLift f θ` (definition module `ConleyZehnder_Setting`) means that $\theta$ is continuous and $f(t)=\exp(i\,\theta(t))$ for all $t$; the square is `unitInterval × unitInterval` with first coordinate $s$ and second coordinate $t$.
-- source:
--   Standard fact on degrees of maps into the circle; used implicitly in Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Section 2

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- For a continuous `F : [0, 1] × [0, 1] → S¹ ⊆ ℂ`, continuous arguments of the four edge
paths satisfy: increment along the left edge `t ↦ F (0, t)` plus increment along the top edge
`s ↦ F (s, 1)` equals increment along the bottom edge `s ↦ F (s, 0)` plus increment along the
right edge `t ↦ F (1, t)`. -/
theorem argLift_square_increment
    (F : C(unitInterval × unitInterval, ℂ)) (hF : ∀ p, ‖F p‖ = 1)
    (a b c d : unitInterval → ℝ)
    (ha : IsArgLift (fun t => F (0, t)) a) (hb : IsArgLift (fun s => F (s, 1)) b)
    (hc : IsArgLift (fun s => F (s, 0)) c) (hd : IsArgLift (fun t => F (1, t)) d) :
    (a 1 - a 0) + (b 1 - b 0) = (c 1 - c 0) + (d 1 - d 0) := by sorry

end ConleyZehnder
