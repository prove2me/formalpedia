-- Prove2me | Theorems.Thm_CollabProject_TimeDep_theorem_5
-- name    : CollabProject.TimeDep.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:42.41028+00:00
-- url     : https://prove2.me/theorems/7c3cd146-4558-47f1-8a93-6fba01d49509
-- title:
--   Theorem 5 — supplier's asymmetric-information decision threshold
-- statement:
--   Suppose the supplier's saving is positive and below its second-period penalty share, with $p^1_1<p^2_1$ and $s_1\ne p^1_1$. These are the two saving regimes (a) $s_1<p^1_1<p^2_1$ and (b) $p^1_1<s_1<p^2_1$. The supplier holds a finite-support belief over manufacturer types in Assumption 2's three classes. If each believed type best-responds after either supplier action, then delaying gives the supplier strictly greater expected payoff exactly when
--
--   $$
--   s_1>p^1_1q^l_0+p^2_1q^h_0.
--   $$
--
--   The selected equilibrium decision is to delay precisely above that threshold and to keep at or below it. This gives the supplier's decision threshold used in the information comparison.
--
--   **Formalization Note** The class probabilities are masses computed from the belief, not independent parameters. Equality makes both actions optimal under weak best response; `IsChosenAction` implements the paper's “keep otherwise” selection at that tie using expected payoffs, not the threshold formula.
-- source:
--   Song, Zhao & Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN preprint (abstract 2980139, PDF of 2019-10-14; published in Manufacturing & Service Operations Management, 2020), p. 17 (PDF 17), Theorem 5; proof, Appendix p. 5 (PDF 37)

import Mathlib
import Definitions.Def_CollabProject_TimeDep_Model

namespace CollabProject.TimeDep

/-- Theorem 5: the supplier's decision in the two below-second-penalty
saving regimes, selecting keep when both actions have equal expected payoff. -/
theorem theorem_5 {ι : Type} [Fintype ι] (S : SType) (B : Belief ι)
    (hS : 0 < S.s1 ∧ S.p11 < S.p21 ∧ S.s1 < S.p21 ∧ S.s1 ≠ S.p11)
    (hB : ∀ i, (B.θ i).Classed) :
    ∀ (σ : ι → Act → Act), (∀ i a, IsBR0 (B.θ i) a (σ i a)) →
      (IsChosenAction S B σ .delay ↔
        S.p11 * qLow B + S.p21 * qHigh B < S.s1) ∧
      (IsChosenAction S B σ .keep ↔
        S.s1 ≤ S.p11 * qLow B + S.p21 * qHigh B) := by sorry

end CollabProject.TimeDep
