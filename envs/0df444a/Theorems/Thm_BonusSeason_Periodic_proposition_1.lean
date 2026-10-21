-- Prove2me | Theorems.Thm_BonusSeason_Periodic_proposition_1
-- name    : BonusSeason.Periodic.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:24.333894+00:00
-- url     : https://prove2.me/theorems/7ba3b7b4-e10b-4127-82e6-073a8b3a89f7
-- title:
--   Proposition 1, p. 28 (PDF 29) — periodic quitting is the unique Pareto optimal plan if α ∈ (α̲, ᾱ) and is not optimal if α ∉ [α̲, ᾱ]
-- statement:
--   Assume the standing assumptions and A1, let the labor market be periodic (the market state solves the periodic market equations) and let the values solve (16)–(25). Write $\Gamma_s=U_s+V_s$.
--
--   1. If $\underline\alpha<\alpha<\overline\alpha$, every turnover plan other than the periodic one gives a newly matched pair a strictly smaller joint value than the periodic plan, both for an odd-period match ($J_1+W_1$) and for an even-period match ($J_2+W_2$). Hence all Pareto optimal contracts induce quitting only at the end of even periods.
--   2. If $\alpha<\underline\alpha$ or $\alpha>\overline\alpha$, the periodic plan is not Pareto optimal: some turnover plan gives a newly matched pair a strictly larger joint value.
--
--   **Formalization Note** The paper prints the second interval as $[\overline\alpha,\underline\alpha]$; its proof (p. 53) has $[\underline\alpha,\overline\alpha]$, which is stated here. Turnover plans are those stationary across periods of the same parity, with satisfied workers never quitting.
-- source:
--   Van Wesep & Waters, Bonus season: A theory of periodic labor markets and coordinated bonuses, SSRN 3124536 (version of January 13, 2021), p. 28 (PDF 29), Proposition 1; proof, pp. 51–53 (PDF 52–54)

import Mathlib
import Definitions.Def_BonusSeason_Periodic_Model

namespace BonusSeason.Periodic

/-- Proposition 1, p. 28: if `α ∈ (α̲, ᾱ)`, every other turnover plan gives a newly matched
pair a strictly lower joint value than the periodic plan, in both periods; if `α ∉ [α̲, ᾱ]`, the
periodic plan is not Pareto optimal. -/
theorem proposition_1 (P : Params) (hP : P.Standing) (m : ℝ → ℝ → ℝ) (hm : MatchingA1 m)
    (L : MarketState) (hL : L.Solves P m) (X : Values) (hX : X.Solves P L m) :
    (alphaLow P m L < P.matchImportance ∧ P.matchImportance < alphaHigh P m L →
      ∀ (a : Plan) (Y : JointValues), a ≠ periodicPlan →
        PlanValues P (X.U₁ + X.V₁) (X.U₂ + X.V₂) a Y →
        Y.x1L < X.J₁ + X.W₁ ∧ Y.x2L < X.J₂ + X.W₂) ∧
    (P.matchImportance < alphaLow P m L ∨ alphaHigh P m L < P.matchImportance →
      ¬ PeriodicPlanOptimal P X) := by sorry
end BonusSeason.Periodic
