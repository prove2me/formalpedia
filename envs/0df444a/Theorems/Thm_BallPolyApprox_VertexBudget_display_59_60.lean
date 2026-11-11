-- Prove2me | Theorems.Thm_BallPolyApprox_VertexBudget_display_59_60
-- name    : BallPolyApprox.VertexBudget.display_59_60
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:54:25.44721+00:00
-- url     : https://prove2.me/theorems/b48a83ba-f940-4ed1-a16f-383fb857d8d4
-- title:
--   §5.3.4 (59)–(60) — errors close to one: $\Delta_d(P)\ge1-2e^{-a}-2Ne^{-c\sqrt d/a}$
-- statement:
--   There are absolute constants $C,c>0$ such that for every $d\ge2$ and every polytope $P\subset\mathbb R^d$ with at most $N$ vertices: for every $0<w<1$,
--   $$\Delta_d(P)\ge1-2(1-w)^{d/2}-2N\exp\Big(-\frac{d(1-w)}{8(1+Cd^{3/2}w)}\Big)\quad(59),$$
--   and for every $1\le a\le d/4$,
--   $$\Delta_d(P)\ge1-2e^{-a}-2Ne^{-c\sqrt d/a}\quad(60).$$
--   (For lower-dimensional $P$ both hold trivially, since then $\Delta_d(P)=1$.)
--
--   Differences from the source:
--   - reading: dimension range of (59)–(60) not printed → every d ≥ 2; reason: the argument applies Lemma 20 with k = d + 1 ≥ 3 and nothing else restricts d; (60) is vacuous for d < 4
--   - encoding: P a polytope with at most N vertices → P = conv V with |V| ≤ N, any finite V ⊂ ℝ^d (lower-dimensional hulls included); reason: the vertex set of conv V is a subset of V
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), §5.3.4, displays (59)–(60), pp. 23–24 (PDF 25–26)

import Mathlib
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError

set_option autoImplicit false

namespace BallPolyApprox.VertexBudget

/-- §5.3.4, displays (59)–(60) (pp. 23–24, PDF 25–26): there are absolute constants `C, c > 0`
such that for every `d ≥ 2` and every polytope `P ⊂ ℝ^d` with at most `N` vertices,
`Δ_d(P) ≥ 1 − 2(1 − w)^{d/2} − 2N exp(−d(1 − w)/(8(1 + C d^{3/2} w)))` for every `0 < w < 1` (59),
and `Δ_d(P) ≥ 1 − 2e^{−a} − 2N e^{−c√d/a}` for every `1 ≤ a ≤ d/4` (60). -/
theorem display_59_60 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      (∀ d : ℕ, 2 ≤ d → ∀ w : ℝ, 0 < w → w < 1 → ∀ N : ℕ, ∀ V : Finset (Rd d), V.card ≤ N →
        1 - 2 * (1 - w) ^ ((d : ℝ) / 2) -
            2 * (N : ℝ) * Real.exp (-((d : ℝ) * (1 - w) /
              (8 * (1 + C * (d : ℝ) ^ ((3 : ℝ) / 2) * w)))) ≤
          ballErr (polytope V)) ∧
      (∀ d : ℕ, 2 ≤ d → ∀ a : ℝ, 1 ≤ a → a ≤ (d : ℝ) / 4 → ∀ N : ℕ, ∀ V : Finset (Rd d),
        V.card ≤ N →
          1 - 2 * Real.exp (-a) - 2 * (N : ℝ) * Real.exp (-(c * Real.sqrt d / a)) ≤
            ballErr (polytope V)) := by sorry

end BallPolyApprox.VertexBudget
