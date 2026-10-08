-- Prove2me | Theorems.Thm_ErrBoundCplx_KLEB_theorem_1_i_ii
-- name    : ErrBoundCplx.KLEB.theorem_1_i_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:38.849247+00:00
-- url     : https://prove2.me/theorems/c9d8ea06-ec41-4b98-b516-71c6f2b0b8d9
-- title:
--   Theorem 1 i)–ii) — subgradient curves move along −∂⁰f, and d/dt f(χ(t⁺)) = −‖χ̇(t⁺)‖² for every t > 0
-- statement:
--   Let $H$ be a real Hilbert space and let $f : H \to (-\infty, +\infty]$ be proper, convex and lower semicontinuous, with $\min f = 0$. Let $x \in \overline{\operatorname{dom} f}$ and let $\chi_x$ be a subgradient curve of $f$ issued from $x$. Then for every $t > 0$ the point $\chi_x(t)$ lies in $\operatorname{dom} \partial f$, and, writing $\partial^0 f(\chi_x(t))$ for the least-norm element of $\partial f(\chi_x(t))$:
--
--   1. the right derivative of $\chi_x$ at $t$ exists and
--   $$\frac{d}{dt}\chi_x(t^+) = -\partial^0 f(\chi_x(t));$$
--   2. the right derivative of $t \mapsto f(\chi_x(t))$ at $t$ exists and
--   $$\frac{d}{dt} f(\chi_x(t^+)) = -\|\dot\chi_x(t^+)\|^2 = -\|\partial^0 f(\chi_x(t))\|^2.$$
--
--   Part 1 says that the curve follows the steepest-descent direction at every positive time, not only almost everywhere; part 2 is the energy identity that turns the KL inequality into a bound on the length of the curve.
--
--   **Formalization Note** The least-norm subgradient is given as a vector $p$ with `IsLeastNormSubgrad f (χ t) p`; its existence encodes $\chi_x(t) \in \operatorname{dom}\partial f$. Right derivatives are derivatives within $[t, \infty)$. The value $f(\chi_x(s))$ is finite for $s \ge t > 0$ and enters as a real number through `toReal`. The middle term $-\|\dot\chi_x(t^+)\|^2$ of the page equals $-\|p\|^2$ by part 1, and is stated in that form.
-- source:
--   arXiv:1510.08234v3, Theorem 1 i), ii), p. 5

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_ErrBoundCplx_KLEB_Setting
open MoreauProx.Characterization

namespace ErrBoundCplx.KLEB

/-- Theorem 1 i)–ii) (Brézis), p. 5: along a subgradient curve issued from `x ∈ cl(dom f)`, at
every time `t > 0` the point `χ(t)` lies in `dom ∂f`, the right derivative of `χ` at `t` is
`−∂⁰f(χ(t))`, and the right derivative of `f ∘ χ` at `t` is `−‖χ̇(t⁺)‖² = −‖∂⁰f(χ(t))‖²`. -/
theorem theorem_1_i_ii {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → EReal) (hf : GammaZero f) (hmin : MinIsZero f)
    (x : H) (hx : x ∈ closure {y : H | f y ≠ ⊤}) (χ : ℝ → H) (hχ : IsSubgradCurve f x χ)
    (t : ℝ) (ht : 0 < t) :
    ∃ p : H, IsLeastNormSubgrad f (χ t) p ∧
      HasDerivWithinAt χ (-p) (Set.Ici t) t ∧
      HasDerivWithinAt (fun s => (f (χ s)).toReal) (-(‖p‖ ^ 2)) (Set.Ici t) t := by sorry

end ErrBoundCplx.KLEB
