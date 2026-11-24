-- Prove2me | Theorems.Thm_DelaunayStretch_prop67_central_residual
-- name    : DelaunayStretch.prop67_central_residual
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T07:35:18.50859+00:00
-- url     : https://prove2.me/theorems/79466132-c828-4445-9b54-2cdb9e82ce27
-- title:
--   (H4) for $H_\star$, central piece: $E^c_{U_0}\le0$ on the accessible set
-- statement:
--   Let $H_\star$ be the explicit function of Theorem 5.1, $U_0=1.59485994$, and let $E^c_{U_0}$ be the residual (6.1) of its central piece. For every $\gamma\in[0,\frac\pi2)$, $(a,b)\in[0,1]^2$ and $\xi\in[-1,1]$ satisfying the accessibility condition (6.2), $|k(\gamma)\xi-\varphi|\le\sin\theta$,
--
--   $$
--   E^c_{U_0}(\gamma,a,b,\xi)\le0 .
--   $$
--
--   This is the central-piece part of (6.3), which by Lemma 6.1(2) gives condition (H4) for $H_\star$ (Proposition 6.7). The inequality holds with equality on the corner curve $(a,b,\xi)=(0,1,1)$ (Lemma 6.2). The paper verifies it with a cover of boxes and the corner lemma 6.5.
-- source:
--   Mo, Cheng, Ding, arXiv:2609.07979v6, Proposition 6.7 (p.43) in the form (6.3) of Lemma 6.1(2) (p.39); certified in the paper by the covers of Table 4 (pp.44–45)

import Mathlib
import Definitions.Def_DelaunayStretch_PieceResiduals

namespace DelaunayStretch

/-- **(6.3), central piece** (Lemma 6.1(2), p.39; Proposition 6.7): `E^c_{U₀}(γ, a, b, ξ) ≤ 0` at every accessible point with `0 ≤ γ < π/2`, `(a, b) ∈ [0, 1]²`, `|ξ| ≤ 1`. -/
theorem prop67_central_residual :
    ∀ γ a b ξ : ℝ, 0 ≤ γ → γ < Real.pi / 2 → 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → |ξ| ≤ 1 →
      Accessible γ a b ξ → resC (159485994 / 100000000) γ a b ξ ≤ 0 := by sorry

end DelaunayStretch
