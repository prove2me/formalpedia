-- Prove2me | Theorems.Thm_DelaunayStretch_check_5_11_c_monotonicity
-- name    : DelaunayStretch.check_5_11_c_monotonicity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T03:14:36.344933+00:00
-- url     : https://prove2.me/theorems/16001d64-492f-43a1-ae83-22bc76144890
-- title:
--   Proposition 5.11(c): monotonicity of $V_\star\pm\frac25R_\star$ in $a$ and $b$
-- statement:
--   Here $V,R,B,D$ are the coefficient functions of Definition 5.2 for the explicit function $H_\star$ of Theorem 5.1 (definition `DelaunayStretch_HstarCoefficients`), $\sigma(\gamma)=\gamma-\cos^2\gamma\,V(\gamma,0,1)$, $k(\gamma)=\frac\pi2-\cos\gamma$ and $U_0=1.59485994$.
--
--   On $[0,\frac\pi2]\times[0,1]^2$, for both signs,
--
--   $$
--   \partial_a\big(V\pm\tfrac25R\big)\ge0,\qquad \partial_b\big(V\pm\tfrac25R\big)\ge0 .
--   $$
--
--   With Lemma 5.9, this gives (H2) for $H_\star$. The paper checks it in exact rational arithmetic: the derivatives are written in the product Bernstein basis on each spline interval and subdivided until all Bernstein coefficients are nonnegative.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, arXiv:2609.07979v6, Proposition 5.11(c) (p.38); docs/VERIFICATION.md §2.3 of the archive

import Mathlib
import Definitions.Def_DelaunayStretch_HstarCoefficients

namespace DelaunayStretch

/-- **Proposition 5.11(c)** (p.38): the hypothesis of Lemma 5.9 for `H⋆`: `∂_a(V ± (2/5)R) ≥ 0` and `∂_b(V ± (2/5)R) ≥ 0` on `[0, π/2] × [0, 1]²`. -/
theorem check_5_11_c_monotonicity :
    ∀ γ a b : ℝ, 0 ≤ γ → γ ≤ Real.pi / 2 → 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      ∀ s : ℝ, (s = 2 / 5 ∨ s = -(2 / 5)) →
        0 ≤ deriv (fun a' => familyV hstarV γ a' b + s * familyR hstarR γ a' b) a ∧
        0 ≤ deriv (fun b' => familyV hstarV γ a b' + s * familyR hstarR γ a b') b := by sorry

end DelaunayStretch
