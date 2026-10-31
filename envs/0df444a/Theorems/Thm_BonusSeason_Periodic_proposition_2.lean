-- Prove2me | Theorems.Thm_BonusSeason_Periodic_proposition_2
-- name    : BonusSeason.Periodic.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:18.627805+00:00
-- url     : https://prove2.me/theorems/812e311d-2ba2-4399-8182-9fdc8b6df604
-- title:
--   Proposition 2, p. 28 (PDF 29) — a periodic equilibrium exists if α ∈ (α̲, ᾱ) and does not exist if α ∉ [α̲, ᾱ]
-- statement:
--   Assume the standing assumptions of the model ($M,N>0$, $N\ne M$, $0<x^L<x^H<1$, $\beta,\delta,p,\theta\in(0,1)$) and that the matching function satisfies Assumption A1. Let a market state solve the periodic labor-market equations, and let $\underline\alpha$, $\overline\alpha$ be the thresholds (43)–(44) computed from its matching likelihoods. Let $\alpha=(x^H-x^L)/(1-x^L)$ be the importance of match quality.
--
--   1. If $\underline\alpha<\alpha<\overline\alpha$, a periodic equilibrium exists.
--   2. If $\alpha<\underline\alpha$ or $\alpha>\overline\alpha$, no periodic equilibrium exists (with any market state).
--
--   In a periodic equilibrium, dissatisfied workers quit only at the end of even periods, labor market depth alternates, and pay can be delivered by contracts with a signing bonus and alternating wages: a coordinated "bonus season".
--
--   **Formalization Note** The paper states "exists if and only if $\alpha\in(\underline\alpha,\overline\alpha)$" while its proof shows existence exactly for $\underline\alpha\le\alpha\le\overline\alpha$; at the endpoints the periodic plan is still weakly Pareto optimal, so the two clauses above are what statement and proof jointly support and the endpoints are left open. The thresholds are computed from a solution of the market equations, which exists and is unique by Lemma 2. Nothing assumes $\underline\alpha<\overline\alpha$.
-- source:
--   Van Wesep & Waters, Bonus season: A theory of periodic labor markets and coordinated bonuses, SSRN 3124536 (version of January 13, 2021), p. 28 (PDF 29), Proposition 2; proof, p. 53 (PDF 54)

import Mathlib
import Definitions.Def_BonusSeason_Periodic_Model

namespace BonusSeason.Periodic

/-- Proposition 2, p. 28: a periodic equilibrium exists if `α ∈ (α̲, ᾱ)` and does not exist
if `α ∉ [α̲, ᾱ]`, the thresholds computed from the (unique, by Lemma 2) periodic labor-market
state. -/
theorem proposition_2 (P : Params) (hP : P.Standing) (m : ℝ → ℝ → ℝ) (hm : MatchingA1 m)
    (L : MarketState) (hL : L.Solves P m) :
    (alphaLow P m L < P.matchImportance ∧ P.matchImportance < alphaHigh P m L →
      PeriodicEquilibrium P m) ∧
    (P.matchImportance < alphaLow P m L ∨ alphaHigh P m L < P.matchImportance →
      ¬ PeriodicEquilibrium P m) := by sorry
end BonusSeason.Periodic
