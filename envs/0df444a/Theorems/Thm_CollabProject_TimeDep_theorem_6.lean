-- Prove2me | Theorems.Thm_CollabProject_TimeDep_theorem_6
-- name    : CollabProject.TimeDep.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:40.688583+00:00
-- url     : https://prove2.me/theorems/183b3307-8ec9-4be2-bd29-5aa7c2bee5f8
-- title:
--   Theorem 6 — exact conditions for information asymmetry to shorten the project
-- statement:
--   In the two-firm serial project with time-dependent delay penalties, compare the project's delay under symmetric and asymmetric information. Under symmetry, the supplier and manufacturer play a subgame-perfect equilibrium using the true cost types. Under asymmetry, the supplier maximizes expected payoff against a belief over manufacturer types; the manufacturer then best-responds using its true cost type. For every equilibrium choice in each information regime, the asymmetric project has strictly fewer delayed periods if and only if
--
--   $$
--   p^1_1<s_1<p^2_1,\qquad s_0<p^1_0<p^2_0,\qquad
--   s_1<p^1_1q^l_0+p^2_1q^h_0.
--   $$
--
--   Here $q^l_0$ and $q^h_0$ are the supplier's belief masses on low-saving and high-saving manufacturer types. The result identifies precisely when uncertainty about the manufacturer's costs improves project duration.
--
--   **Formalization Note** Positive savings and genericity at the payoff thresholds are explicit. The additional condition $s_1\ne p^1_1q^l_0+p^2_1q^h_0$ excludes a tie at which the source's printed if-and-only-if is ambiguous: Theorem 5 selects keep at equality, while a weak equilibrium permits both actions. The true manufacturer type need not belong to the belief's support; believed types need not satisfy Condition 2's global-optimum inequality. Delay counts are derived from actions, and class masses are derived from the belief.
-- source:
--   Song, Zhao & Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN preprint (abstract 2980139, PDF of 2019-10-14; published in Manufacturing & Service Operations Management, 2020), p. 17 (PDF 17), Theorem 6; proof, Appendix p. 5 (PDF 37)

import Mathlib
import Definitions.Def_CollabProject_TimeDep_Model

namespace CollabProject.TimeDep

/-- Theorem 6: asymmetric information strictly shortens the actual project's
duration precisely under the paper's three conditions. -/
theorem theorem_6 {ι : Type} [Fintype ι]
    (S : SType) (M : MType) (B : Belief ι)
    (h : Standing S M) (hG : Generic S M)
    (hB : ∀ i, (B.θ i).Classed)
    (htie : S.s1 ≠ S.p11 * qLow B + S.p21 * qHigh B) :
    (∀ (a1 : Act) (σ0 : Act → Act) (b1 : Act)
      (σ : ι → Act → Act) (τ0 : Act → Act),
      IsSPNE S M a1 σ0 → IsAsymEq S B M b1 σ τ0 →
      delayCount b1 (τ0 b1) < delayCount a1 (σ0 a1)) ↔
      (S.p11 < S.s1 ∧ S.s1 < S.p21 ∧ M.s0 < M.p10 ∧ M.p10 < M.p20 ∧
       S.s1 < S.p11 * qLow B + S.p21 * qHigh B) := by sorry

end CollabProject.TimeDep
