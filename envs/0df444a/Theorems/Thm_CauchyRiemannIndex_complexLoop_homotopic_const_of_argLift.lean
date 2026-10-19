-- Prove2me | Theorems.Thm_CauchyRiemannIndex_complexLoop_homotopic_const_of_argLift
-- name    : CauchyRiemannIndex.complexLoop_homotopic_const_of_argLift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T16:49:18.247901+00:00
-- url     : https://prove2.me/theorems/d0ddfdee-33a8-4720-8d9c-c11cb7909175
-- title:
--   Loops in $\mathbb C\setminus\{0\}$ of winding number zero are null-homotopic rel base point
-- statement:
--   Let $v:[0,1]\to\mathbb C\setminus\{0\}$ be continuous with $v(1)=v(0)$, and let $\theta:[0,1]\to\mathbb R$ be a continuous argument of its direction, i.e. $v(t)/|v(t)|=e^{i\theta(t)}$ for all $t$. If
--   $$\theta(1)=\theta(0),$$
--   then there is a continuous map $H:[0,1]\times[0,1]\to\mathbb C\setminus\{0\}$ with
--   $$H(0,t)=v(t),\qquad H(1,t)=v(0),\qquad H(s,0)=H(s,1)=v(0).$$
--
--   This is the statement that a based loop in the punctured plane with winding number zero is null-homotopic relative to its base point, i.e. the winding number is injective on $\pi_1(\mathbb C\setminus\{0\})$.
--
--   **Formalization Note.** The argument condition is `IsArgLift (fun t => v t / ‖v t‖) θ` from the setting definitions (`θ` continuous and `v t / ‖v t‖ = exp (θ t * I)`); the homotopy is `H : C(unitInterval × unitInterval, ℂ)` with `H p ≠ 0` for every `p`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, p. 62 (auxiliary fact for Theorem 3.34: the fundamental group of $\mathrm{Sp}(2n)$)

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open Matrix

/-- A loop in `ℂ ∖ {0}` whose direction `v / |v|` has a continuous argument with equal end
values is homotopic to the constant loop through loops in `ℂ ∖ {0}` with the same base point. -/
theorem complexLoop_homotopic_const_of_argLift (v : C(unitInterval, ℂ)) (hv : ∀ t, v t ≠ 0)
    (h1 : v 1 = v 0) (θ : unitInterval → ℝ)
    (hθ : IsArgLift (fun t => v t / (‖v t‖ : ℂ)) θ) (hθ1 : θ 1 = θ 0) :
    ∃ H : C(unitInterval × unitInterval, ℂ), (∀ t, H (0, t) = v t) ∧ (∀ t, H (1, t) = v 0) ∧
      (∀ p, H p ≠ 0) ∧ (∀ s, H (s, 0) = v 0) ∧ ∀ s, H (s, 1) = v 0 := by sorry

end CauchyRiemannIndex
