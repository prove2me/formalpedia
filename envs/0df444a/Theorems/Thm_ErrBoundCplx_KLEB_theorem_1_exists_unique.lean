-- Prove2me | Theorems.Thm_ErrBoundCplx_KLEB_theorem_1_exists_unique
-- name    : ErrBoundCplx.KLEB.theorem_1_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:02:51.196493+00:00
-- url     : https://prove2.me/theorems/1bb87b7d-e524-4d1d-ad2a-f317bd4842c3
-- title:
--   Theorem 1 (Brézis, Bruck) — from every x ∈ cl(dom f) issues a unique subgradient curve
-- statement:
--   Let $H$ be a real Hilbert space and let $f : H \to (-\infty, +\infty]$ be proper, convex and lower semicontinuous, with $\min f = 0$. Let $x$ belong to the closure $\overline{\operatorname{dom} f}$ of the effective domain $\operatorname{dom} f = \{y : f(y) < +\infty\}$.
--
--   Then there is a curve $\chi_x : [0, \infty) \to H$, continuous on $[0, \infty)$ and absolutely continuous on every compact subinterval of $(0, \infty)$, with
--   $$\chi_x(0) = x, \qquad \dot\chi_x(t) \in -\partial f(\chi_x(t)) \quad \text{for almost every } t > 0,$$
--   and any two such curves coincide on $[0, \infty)$.
--
--   This is the existence and uniqueness part of the Brézis–Bruck theorem, which defines the subgradient semiflow $(t, x) \mapsto \chi_x(t)$ used throughout §6.1 and in the proof of Theorem 5.
--
--   **Formalization Note** "Subgradient curve" is the predicate `IsSubgradCurve` of `ErrBoundCplx.KLEB.Setting`. The page calls $\chi_x$ "absolutely continuous on $[0, \infty)$"; it is formalized as continuity on $[0, \infty)$ plus absolute continuity on every $[a, b] \subset (0, \infty)$, which is Brézis' notion for initial points in $\overline{\operatorname{dom} f}$ (absolute continuity up to $t = 0$ can fail when $f(x) = +\infty$). The standing normalization $\min f = 0$ of §2 is kept as a hypothesis.
-- source:
--   arXiv:1510.08234v3, Theorem 1 (first sentence), p. 5

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_ErrBoundCplx_KLEB_Setting
open MoreauProx.Characterization

namespace ErrBoundCplx.KLEB

/-- Theorem 1 (Brézis, Bruck), p. 5, existence and uniqueness: for every `x ∈ cl(dom f)` there
is a subgradient curve issued from `x`, and two subgradient curves issued from `x` coincide on
`[0, ∞)`. -/
theorem theorem_1_exists_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → EReal) (hf : GammaZero f) (hmin : MinIsZero f)
    (x : H) (hx : x ∈ closure {y : H | f y ≠ ⊤}) :
    (∃ χ : ℝ → H, IsSubgradCurve f x χ) ∧
      ∀ χ₁ χ₂ : ℝ → H, IsSubgradCurve f x χ₁ → IsSubgradCurve f x χ₂ →
        Set.EqOn χ₁ χ₂ (Set.Ici 0) := by sorry

end ErrBoundCplx.KLEB
