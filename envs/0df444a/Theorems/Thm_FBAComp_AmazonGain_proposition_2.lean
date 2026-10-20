-- Prove2me | Theorems.Thm_FBAComp_AmazonGain_proposition_2
-- name    : FBAComp.AmazonGain.proposition_2
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:14.410486+00:00
-- url     : https://prove2.me/theorems/2f253300-ff54-431c-9b05-b04251e34968
-- title:
--   Proposition 2, p. 19 — Amazon benefits for small or large sensitivity
-- statement:
--   Under the standing parameters and positive no-FBA seller sales throughout $(0,\alpha)$, there are thresholds $0<\underline\eta\leq\bar\eta$ such that, for every $\eta\in(0,\alpha)$ and every pair of no-FBA and fee-optimal FBA equilibria,
--
--   $$\Pi_{A,F}^*(\eta)\geq\Pi_{A,N}^*(\eta)\iff\eta\leq\underline\eta\ \text{or}\ \eta\geq\bar\eta.$$
--
--   Thus Amazon benefits at small or large cross-service sensitivity and loses at moderate sensitivity when that loss interval intersects the model's domain.
--
--   **Formalization Note.** The theorem uses equilibrium relations from §4.1, including the fee problem (5), instead of defining equilibrium by the appendix solutions. Fee feasibility includes nonnegative seller sales. The positive market bases, nonnegative costs and interior condition are disclosed additions. The upper threshold need not lie below $\alpha$.
-- source:
--   Lai, Liu, Xiao & Zhao, “Fulfilled by Amazon”, SSRN preprint 3270958 (PDF of 2021-10-08), p. 19, Proposition 2

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_Model

namespace FBAComp.AmazonGain

/-- Proposition 2, p. 19: two sensitivity thresholds characterize when Amazon's
equilibrium profit with FBA is at least its profit without FBA. -/
theorem proposition_2 (P : Params) (hP : P.Standing) (hI : Interior P) :
    ∃ ηlo ηhi : ℝ, 0 < ηlo ∧ ηlo ≤ ηhi ∧
      ∀ η ∈ Set.Ioo 0 P.α, ∀ wN pAN pSN T wF pAF pSF : ℝ,
        IsEqN P η wN pAN pSN →
        IsFeeOptimal P η (profitSN P η pAN pSN) T wF pAF pSF →
        (profitAN P η wN pAN pSN ≤ profitAF P η T wF pAF pSF ↔
          η ≤ ηlo ∨ ηhi ≤ η) := by sorry

end FBAComp.AmazonGain
