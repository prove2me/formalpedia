-- Prove2me | Theorems.Thm_DelaunayStretch_check_5_11_d_H3_inequality
-- name    : DelaunayStretch.check_5_11_d_H3_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-24T03:14:29.942229+00:00
-- url     : https://prove2.me/theorems/429e4585-3841-4731-81e0-426891985e89
-- title:
--   Proposition 5.11(d): inequality (5.11) for $H_\star$ at level $U_0$
-- statement:
--   Here $V,R,B,D$ are the coefficient functions of Definition 5.2 for the explicit function $H_\star$ of Theorem 5.1 (definition `DelaunayStretch_HstarCoefficients`), $\sigma(\gamma)=\gamma-\cos^2\gamma\,V(\gamma,0,1)$, $k(\gamma)=\frac\pi2-\cos\gamma$ and $U_0=1.59485994$.
--
--   For every $\gamma\in[0,\frac\pi2)$, at $\xi=\gamma/k(\gamma)$,
--
--   $$
--   \cos^2\gamma\,V(\gamma,0,0)+\sigma(\gamma)\,\xi+\cos^2\gamma\big[B(\gamma)(\xi-\xi^3)+D(\gamma)(\xi^3-\xi^5)\big]\ge\tfrac\pi2-U_0\cos\gamma .
--   $$
--
--   With Lemma 5.10, this gives (H3) for $H_\star$. The paper checks it with interval arithmetic in $\gamma$, using a form without removable singularities near $\gamma=\frac\pi2$.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, arXiv:2609.07979v6, Proposition 5.11(d) (p.38); docs/VERIFICATION.md §2.5 of the archive

import Mathlib
import Definitions.Def_DelaunayStretch_HstarCoefficients

namespace DelaunayStretch

/-- **Proposition 5.11(d)** (p.38): the inequality (5.11) for `H⋆` with `U = U₀ = 1.59485994`, for all `γ ∈ [0, π/2)`. -/
theorem check_5_11_d_H3_inequality :
    ∀ γ : ℝ, 0 ≤ γ → γ < Real.pi / 2 →
      Real.pi / 2 - (159485994 / 100000000 : ℝ) * Real.cos γ ≤
        Real.cos γ ^ 2 * familyV hstarV γ 0 0 +
          (γ - Real.cos γ ^ 2 * familyV hstarV γ 0 1) * (γ / (Real.pi / 2 - Real.cos γ)) +
          Real.cos γ ^ 2 * (familySpline hstarB γ * ((γ / (Real.pi / 2 - Real.cos γ)) -
              (γ / (Real.pi / 2 - Real.cos γ)) ^ 3) +
            familySpline hstarD γ * ((γ / (Real.pi / 2 - Real.cos γ)) ^ 3 -
              (γ / (Real.pi / 2 - Real.cos γ)) ^ 5)) := by sorry

end DelaunayStretch
