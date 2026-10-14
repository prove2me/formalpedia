-- Prove2me | Theorems.Thm_FlatlyFoliated_theorem3_arrow_of_time
-- name    : FlatlyFoliated.theorem3_arrow_of_time
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T20:40:24.667327+00:00
-- url     : https://prove2.me/theorems/30d9c842-8ec9-4575-a1ef-d0507b4852b5
-- title:
--   Theorem 3 — $\Lambda>0$ gives a geometric arrow of time
-- statement:
--   Let $\Lambda>0$, let $\mu\ge0$ and $J$ be smooth, and let smooth $(\omega,\eta)$ with $\eta>0$ solve the FFR equations (34)–(35). Then the mean curvature $K=(\nabla\cdot\omega)/\eta$ of the flat foliation has a constant strict sign on $\mathbb R^3$:
--   $$\Big(\forall x,\ \frac{\nabla\cdot\omega(x)}{\eta(x)}>0\Big)\ \ \text{or}\ \ \Big(\forall x,\ \frac{\nabla\cdot\omega(x)}{\eta(x)}<0\Big).$$
--
--   Hence the direction of the mean curvature vector $\vec K=Kn$ defines a geometrically preferred arrow of time.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, https://arxiv.org/abs/1911.00967, p. 12, Theorem 3 (eqs. (52)–(53))

import Mathlib
import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff

namespace FlatlyFoliated

/-- Theorem 3: for `Λ > 0`, every `μ ≥ 0` smooth solution has a mean curvature
`K = (∇·w)/η` of constant sign (the geometric arrow of time). -/
theorem theorem3_arrow_of_time (Λ : ℝ) (hΛ : 0 < Λ) (μ : R3 → ℝ) (J : R3 → R3)
    (w : R3 → R3) (η : R3 → ℝ) (hμ : ContDiff ℝ ∞ μ) (hJ : ContDiff ℝ ∞ J)
    (hw : ContDiff ℝ ∞ w) (hη : ContDiff ℝ ∞ η) (hμnn : ∀ x, 0 ≤ μ x)
    (hηpos : ∀ x, 0 < η x) (hsol : FFREquations Λ μ J w η) :
    (∀ x, 0 < divg w x / η x) ∨ (∀ x, divg w x / η x < 0) := by sorry

end FlatlyFoliated
