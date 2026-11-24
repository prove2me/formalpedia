-- Prove2me | Theorems.Thm_DelaunayStretch_prop67_outer_residual
-- name    : DelaunayStretch.prop67_outer_residual
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T07:35:24.410519+00:00
-- url     : https://prove2.me/theorems/bee4ac75-ebcd-47b1-91b5-1f292965c464
-- title:
--   (H4) for $H_\star$, outer piece $\xi\ge1$: $E^+_{U_0}\le0$ where accessible
-- statement:
--   Let $H_\star$ be the explicit function of Theorem 5.1, $U_0=1.59485994$, and let $E^+_{U_0}$ be the residual (6.1) of its outer piece $\xi\ge1$. For every $\gamma\in[0,\frac\pi2)$, $(a,b)\in[0,1]^2$ and $\xi\ge1$ satisfying the accessibility condition (6.2),
--
--   $$
--   E^+_{U_0}(\gamma,a,b)\le0 .
--   $$
--
--   This is the part of (6.3) for the outer piece $\xi\ge1$. The outer piece $\xi\le-1$ follows from it by the reflection $\rho_2$ (identities (6.9)). The inequality holds with equality on the corner curve $(a,b)=(0,1)$ (Lemma 6.2), and the paper uses the corner lemma 6.6 there.
-- source:
--   Mo, Cheng, Ding, arXiv:2609.07979v6, Proposition 6.7 (p.43) in the form (6.3) of Lemma 6.1(2) (p.39); certified in the paper by the covers of Table 4 (pp.44–45)

import Mathlib
import Definitions.Def_DelaunayStretch_PieceResiduals

namespace DelaunayStretch

/-- **(6.3), outer piece `ξ ≥ 1`** (Lemma 6.1(2), p.39; Proposition 6.7): `E^+_{U₀}(γ, a, b) ≤ 0` whenever some `ξ ≥ 1` is accessible, `0 ≤ γ < π/2`, `(a, b) ∈ [0, 1]²`. -/
theorem prop67_outer_residual :
    ∀ γ a b ξ : ℝ, 0 ≤ γ → γ < Real.pi / 2 → 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → 1 ≤ ξ →
      Accessible γ a b ξ → resOut (159485994 / 100000000) 1 γ a b ≤ 0 := by sorry

end DelaunayStretch
