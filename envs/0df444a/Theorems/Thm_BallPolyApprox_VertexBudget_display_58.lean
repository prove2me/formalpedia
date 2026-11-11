-- Prove2me | Theorems.Thm_BallPolyApprox_VertexBudget_display_58
-- name    : BallPolyApprox.VertexBudget.display_58
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:54:32.585438+00:00
-- url     : https://prove2.me/theorems/c864a645-971e-46d8-9a3f-9a50788756ae
-- title:
--   §5.3.3 (58) — covering bound $\log(2N)\ge d/(4(1+2\zeta))$ and $\log(2N)\ge\frac{d-1}2\log\frac1{3\zeta}$ for $\zeta\le1/4$
-- statement:
--   There are absolute constants $C_{\mathrm{cov}}>0$ (large) and $0<\varepsilon_0\le1/16$ (small) such that, for every $d\ge3$, every polytope $P\subset\mathbb R^d$ with at most $N$ vertices and every $\varepsilon$ with $\Delta_d(P)\le\varepsilon\le\varepsilon_0$, setting $\zeta=C_{\mathrm{cov}}\varepsilon\sqrt d$,
--   $$\log(2N)\ge\frac d{4(1+2\zeta)},\qquad\log(2N)\ge\frac{d-1}2\log\frac1{3\zeta}\quad(\zeta\le\tfrac14)\quad(58).$$
--
--   Differences from the source:
--   - reading: We fix a large absolute constant C_cov and a small absolute constant ε_0 ≤ 1/16; d not restricted in the display → ∃ C_cov > 0, ∃ ε_0 ∈ (0, 1/16], for every d ≥ 3; reason: the proof fixes these constants once; the deduction of Theorem 2, which holds for every d ≥ 3, applies (58) for every d ≥ 3
--   - encoding: P a polytope with at most N vertices → P = conv V with |V| ≤ N; reason: the vertex set of conv V is a subset of V
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), §5.3.3, display (58), p. 23 (PDF 25)

import Mathlib
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError

set_option autoImplicit false

namespace BallPolyApprox.VertexBudget

/-- §5.3.3, display (58) (p. 23, PDF 25): there are absolute constants `C_cov > 0` and
`0 < ε_0 ≤ 1/16` such that, for every `d ≥ 3`, every polytope `P ⊂ ℝ^d` with at most `N` vertices
and every `ε` with `Δ_d(P) ≤ ε ≤ ε_0`, setting `ζ = C_cov ε √d`:
`log(2N) ≥ d / (4(1 + 2ζ))`, and `log(2N) ≥ ((d − 1)/2) log(1/(3ζ))` when `ζ ≤ 1/4`. -/
theorem display_58 :
    ∃ Ccov ε0 : ℝ, 0 < Ccov ∧ 0 < ε0 ∧ ε0 ≤ 1 / 16 ∧
      ∀ d : ℕ, 3 ≤ d → ∀ N : ℕ, ∀ V : Finset (Rd d), V.card ≤ N → ∀ ε : ℝ,
        ballErr (polytope V) ≤ ε → ε ≤ ε0 →
          (d : ℝ) / (4 * (1 + 2 * (Ccov * ε * Real.sqrt d))) ≤ Real.log (2 * (N : ℝ)) ∧
          (Ccov * ε * Real.sqrt d ≤ 1 / 4 →
            ((d : ℝ) - 1) / 2 * Real.log (1 / (3 * (Ccov * ε * Real.sqrt d))) ≤
              Real.log (2 * (N : ℝ))) := by sorry

end BallPolyApprox.VertexBudget
