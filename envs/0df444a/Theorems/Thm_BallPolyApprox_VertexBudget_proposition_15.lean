-- Prove2me | Theorems.Thm_BallPolyApprox_VertexBudget_proposition_15
-- name    : BallPolyApprox.VertexBudget.proposition_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:55:53.761451+00:00
-- url     : https://prove2.me/theorems/de752ab2-bc39-45ad-80f0-02a9ede13cab
-- title:
--   Proposition 15 — $\beta_m\sim2\sqrt{2/\pi}\,m^{-3/2}$ and $\beta_m\asymp m^{-3/2}$ for all $m\ge1$
-- statement:
--   As $m\to\infty$,
--   $$\beta_m=\Big(2\sqrt{2/\pi}+o(1)\Big)m^{-3/2}\quad(34).$$
--   Moreover, there are absolute constants $c,C>0$ such that $cm^{-3/2}\le\beta_m\le Cm^{-3/2}$ for all $m\ge1$ (35).
--
--   Differences from the source:
--   - encoding: β_m = (2√(2/π) + o(1)) m^{−3/2} as m → ∞ → β_m · m^{3/2} → 2√(2/π) along Filter.atTop; reason: the same asymptotic statement
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), Proposition 15, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError
import Definitions.Def_BallPolyApprox_VertexBudget_SimplexLayer

set_option autoImplicit false

open MeasureTheory

namespace BallPolyApprox.VertexBudget

/-- Proposition 15 (p. 15, PDF 17): as `m → ∞`, `β_m = (2√(2/π) + o(1)) m^{−3/2}` (34), i.e.
`β_m m^{3/2} → 2√(2/π)`; and there are absolute constants `c, C > 0` with
`c m^{−3/2} ≤ β_m ≤ C m^{−3/2}` for all `m ≥ 1` (35). -/
theorem proposition_15 :
    Filter.Tendsto (fun m : ℕ => betaM m * (m : ℝ) ^ ((3 : ℝ) / 2)) Filter.atTop
        (nhds (2 * Real.sqrt (2 / Real.pi))) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
        c * (m : ℝ) ^ (-(3 : ℝ) / 2) ≤ betaM m ∧ betaM m ≤ C * (m : ℝ) ^ (-(3 : ℝ) / 2) := by sorry

end BallPolyApprox.VertexBudget
