-- Prove2me | Theorems.Thm_AronszajnRK_Inclusion_rkClass_inter_and_sum
-- name    : AronszajnRK.Inclusion.rkClass_inter_and_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:29:44.143339+00:00
-- url     : https://prove2.me/theorems/750ec9ff-2616-4e39-99eb-e4722a8d9fd4
-- title:
--   §13 (D), Theorem VI — intersections and sums of (R.K.)-classes are (R.K.)-classes
-- statement:
--   Let $F_1$ and $F_2$ be (R.K.)-classes of complex functions on a set $X$. Then the intersection $F_1\cdot F_2$ and the sum
--
--   $$F_1 + F_2 = \{\, f_1 + f_2 : f_1\in F_1,\ f_2\in F_2 \,\}$$
--
--   are again (R.K.)-classes.
--
--   The (R.K.)-classes on a set are therefore closed under the two lattice-type operations of intersection and sum.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 384, §13 (D), Theorem VI

import Mathlib
import Definitions.Def_AronszajnRK_Inclusion_IsRKClass

namespace AronszajnRK.Inclusion

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §13 (D),
Theorem VI, p. 384 (PDF p. 48). If `F₁` and `F₂` are (R.K.)-classes, then the same is true of the
classes `F₁ · F₂` (the intersection) and `F₁ + F₂` (all sums `f₁ + f₂`, `f₁ ∈ F₁`, `f₂ ∈ F₂`).
`F₁ = Set.range ⇑` of an RKHS `H₁`, `F₂` likewise. -/
theorem rkClass_inter_and_sum {X : Type*} (S₁ S₂ : Set (X → ℂ))
    (h₁ : IsRKClass S₁) (h₂ : IsRKClass S₂) :
    IsRKClass (S₁ ∩ S₂) ∧ IsRKClass {f | ∃ f₁ ∈ S₁, ∃ f₂ ∈ S₂, f = f₁ + f₂} := by sorry

end AronszajnRK.Inclusion
