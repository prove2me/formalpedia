-- Prove2me | Theorems.Thm_ErrBoundCplx_KLEB_theorem_1_iii_iv
-- name    : ErrBoundCplx.KLEB.theorem_1_iii_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:24.781926+00:00
-- url     : https://prove2.me/theorems/c327625c-1b34-44e0-be07-6f2ae56e1c0a
-- title:
--   Theorem 1 iii)–iv) — along a subgradient curve ‖χ(t) − z‖ (z ∈ S) and f(χ(t)) are nonincreasing, and f(χ(t)) → min f
-- statement:
--   Let $H$ be a real Hilbert space and let $f : H \to (-\infty, +\infty]$ be proper, convex and lower semicontinuous, with $\min f = 0$ and $S = \operatorname{argmin} f$. Let $x \in \overline{\operatorname{dom} f}$ and let $\chi_x$ be a subgradient curve of $f$ issued from $x$. Then:
--
--   1. for each $z \in S$, the function $t \mapsto \|\chi_x(t) - z\|$ is nonincreasing on $[0, \infty)$;
--   2. the function $t \mapsto f(\chi_x(t))$ is nonincreasing on $[0, \infty)$, and
--   $$\lim_{t \to \infty} f(\chi_x(t)) = \min f = 0.$$
--
--   Part 1 (Fejér monotonicity with respect to $S$) keeps a curve issued from a ball $B(\bar x, \rho)$ centred at a minimizer inside that ball; part 2 keeps it inside a sublevel band $[f \le r_0]$. Both are used in the proof of Theorem 27.
--
--   **Formalization Note** The page's "decreases" in iii) is read as "is nonincreasing", as in Brézis. Monotonicity is asserted on $[0, \infty)$ only. In part 2, $f(\chi_x(t))$ is compared in `EReal`, since $f(x) = +\infty$ is allowed at $t = 0$, and the limit is taken in `EReal`.
-- source:
--   arXiv:1510.08234v3, Theorem 1 iii), iv), p. 5

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_ErrBoundCplx_KLEB_Setting
open MoreauProx.Characterization Filter Topology

namespace ErrBoundCplx.KLEB

/-- Theorem 1 iii)–iv) (Brézis), p. 5: along a subgradient curve issued from `x ∈ cl(dom f)`,
the distance to each minimizer is nonincreasing on `[0, ∞)`, the value `f(χ(t))` is
nonincreasing on `[0, ∞)`, and `f(χ(t)) → min f = 0` as `t → ∞`. -/
theorem theorem_1_iii_iv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → EReal) (hf : GammaZero f) (hmin : MinIsZero f)
    (x : H) (hx : x ∈ closure {y : H | f y ≠ ⊤}) (χ : ℝ → H) (hχ : IsSubgradCurve f x χ) :
    (∀ z ∈ argminSet f, AntitoneOn (fun t => ‖χ t - z‖) (Set.Ici 0)) ∧
      AntitoneOn (fun t => f (χ t)) (Set.Ici 0) ∧
      Tendsto (fun t => f (χ t)) atTop (𝓝 0) := by sorry

end ErrBoundCplx.KLEB
