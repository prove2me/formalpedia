-- Prove2me | Theorems.Thm_BonusSeason_Periodic_lemma_2
-- name    : BonusSeason.Periodic.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:02.905923+00:00
-- url     : https://prove2.me/theorems/1851a6d0-b483-4f72-a522-c62dcacf5f2a
-- title:
--   Lemma 2, pp. 17–18 (PDF 18–19) — unique periodic matching likelihoods, ordered f₂ < f₁ < g₁ < g₂ if N < M and reversed if M < N
-- statement:
--   Assume the standing assumptions of the model and Assumption A1. Then the periodic labor-market equations (46)–(57) have exactly one solution. In it, the masses $N^0_1,N^0_2$ of unemployed workers and $M^0_1,M^0_2$ of vacant firms are positive, and more workers search at the start of odd periods: $N^0_2<N^0_1$. Moreover, if $N<M$ then
--   $$f_2<f_1<g_1<g_2,$$
--   and if $M<N$ then
--   $$g_2<g_1<f_1<f_2.$$
--
--   The lemma establishes that labor market depth, and hence each side's matching likelihood, oscillates between odd and even periods when dissatisfied workers quit only after even periods.
--
--   **Formalization Note** Uniqueness is stated for the whole market state, which determines $f_s$, $g_s$. Positivity and $N^0_2<N^0_1$ are shown in the paper's proof (pp. 45–47) and on p. 18; they are stated so that the likelihoods, which are quotients, are well defined.
-- source:
--   Van Wesep & Waters, Bonus season: A theory of periodic labor markets and coordinated bonuses, SSRN 3124536 (version of January 13, 2021), pp. 17–18 (PDF 18–19), Lemma 2, eqs. (13)–(14); proof of Lemma 2, pp. 45–48 (PDF 46–49)

import Mathlib
import Definitions.Def_BonusSeason_Periodic_Model

namespace BonusSeason.Periodic

/-- Lemma 2, pp. 17–18, with the facts of its proof (pp. 45–47): the periodic labor-market
equations have a unique solution; in it the masses searching are positive and larger at the start
of odd periods; if `N < M` then `f₂ < f₁ < g₁ < g₂` (13), and if `M < N` then
`g₂ < g₁ < f₁ < f₂` (14). -/
theorem lemma_2 (P : Params) (hP : P.Standing) (m : ℝ → ℝ → ℝ) (hm : MatchingA1 m) :
    (∃! L : MarketState, L.Solves P m) ∧
    ∀ L : MarketState, L.Solves P m →
      0 < L.N0₁ ∧ 0 < L.N0₂ ∧ 0 < L.M0₁ P ∧ 0 < L.M0₂ P ∧ L.N0₂ < L.N0₁ ∧
      (P.N < P.M → L.f₂ P m < L.f₁ P m ∧ L.f₁ P m < L.g₁ P m ∧ L.g₁ P m < L.g₂ P m) ∧
      (P.M < P.N → L.g₂ P m < L.g₁ P m ∧ L.g₁ P m < L.f₁ P m ∧ L.f₁ P m < L.f₂ P m) := by sorry
end BonusSeason.Periodic
