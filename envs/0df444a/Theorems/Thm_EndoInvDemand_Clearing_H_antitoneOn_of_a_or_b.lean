-- Prove2me | Theorems.Thm_EndoInvDemand_Clearing_H_antitoneOn_of_a_or_b
-- name    : EndoInvDemand.Clearing.H_antitoneOn_of_a_or_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:48.552015+00:00
-- url     : https://prove2.me/theorems/47f7b983-a2b8-4748-8eee-8b67387547e2
-- title:
--   Proof of Theorem 3.3, pp. 31–32 — under (a) or (b), H_Z is non-increasing on dom H_Z
-- statement:
--   Let $R$ satisfy Assumption 3.1 on $\mathbb D\in\{\mathbb R,\mathbb R_{++}\}$, let $\mathcal X$ satisfy Assumption 2.1, and let $Z\in L^\infty$. Assume either
--
--   (a) $Z$ and $\mathcal X+Z$ are comonotonic, or
--   (b) $R$ is linear (affine) on $\mathbb D$.
--
--   Then $H_Z$ is non-increasing on $\operatorname{dom}H_Z$: for $v\le w$ in $\operatorname{dom}H_Z$,
--   $$H_Z(w)\le H_Z(v).$$
--
--   Consequently $v\mapsto H_Z(v)-v$ is strictly decreasing, so $H_Z$ has at most one fixed point; this is the uniqueness argument of Theorem 3.3 under (a) or (b).
--
--   **Formalization Note** The paper states $H_Z'(v)\le0$ (a right derivative at the boundary of $\operatorname{dom}H_Z$); the formal statement is the monotonicity this yields, which is what the proofs of Theorem 3.3 and Corollary 3.4 use.
-- source:
--   Bichuch & Feinstein, Endogenous Inverse Demand Functions, arXiv:2012.08002v3, proof of Theorem 3.3 (Online Appendix D.2), pp. 31–32, conditions (a)–(b)

import Mathlib
import Definitions.Def_EndoInvDemand_Clearing_Setting
open MeasureTheory
open scoped ENNReal Topology

namespace EndoInvDemand.Clearing

/-- Proof of Theorem 3.3, pp. 31–32: under condition (a) or (b), `H_Z` is non-increasing on
`dom H_Z` (the page: `H′_Z(v) ≤ 0`, one-sided at the boundary). -/
theorem H_antitoneOn_of_a_or_b {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Dom) (R : ℝ → ℝ) (hR : Assumption31 D R)
    (X Z : Ω → ℝ) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    (h : condA P X Z ∨ condB D R) :
    AntitoneOn (H P D R X Z) (domH P D R X Z) := by sorry

end EndoInvDemand.Clearing
