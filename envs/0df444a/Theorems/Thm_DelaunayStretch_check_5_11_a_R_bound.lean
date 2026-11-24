-- Prove2me | Theorems.Thm_DelaunayStretch_check_5_11_a_R_bound
-- name    : DelaunayStretch.check_5_11_a_R_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-24T03:14:34.59781+00:00
-- url     : https://prove2.me/theorems/ff28c911-9912-44cf-9efd-546775701c58
-- title:
--   Proposition 5.11(a): $|R_\star|\le\frac1{50}$
-- statement:
--   Here $V,R,B,D$ are the coefficient functions of Definition 5.2 for the explicit function $H_\star$ of Theorem 5.1 (definition `DelaunayStretch_HstarCoefficients`), $\sigma(\gamma)=\gamma-\cos^2\gamma\,V(\gamma,0,1)$, $k(\gamma)=\frac\pi2-\cos\gamma$ and $U_0=1.59485994$.
--
--   For all $\gamma\in[0,\frac\pi2]$ and $a,b\in[0,1]$,
--
--   $$
--   |R(\gamma,a,b)|\le\tfrac1{50}.
--   $$
--
--   This bound feeds the reduction of (H1) (Lemma 5.8) with $\bar R=\frac1{50}$. The paper verifies it in exact rational arithmetic from the Bernstein and B-spline coefficients after one bisection of each angular coordinate.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, arXiv:2609.07979v6, Proposition 5.11(a) (p.38); verification §C.4 and docs/VERIFICATION.md §2.2 of the archive

import Mathlib
import Definitions.Def_DelaunayStretch_HstarCoefficients

namespace DelaunayStretch

/-- **Proposition 5.11(a)** (p.38): `|R| ≤ 1/50` on `[0, π/2] × [0, 1]²` for the coefficient function `R` of `H⋆`. -/
theorem check_5_11_a_R_bound :
    ∀ γ a b : ℝ, 0 ≤ γ → γ ≤ Real.pi / 2 → 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      |familyR hstarR γ a b| ≤ 1 / 50 := by sorry

end DelaunayStretch
