-- Prove2me | Theorems.Thm_ConvexRiskFn_Cont_positive_functional_continuous
-- name    : ConvexRiskFn.Cont.positive_functional_continuous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:46.931127+00:00
-- url     : https://prove2.me/theorems/944e36a9-b2be-4e70-884c-5871b250da08
-- title:
--   Levin [11, Theorem 0.12], as used on p. 437 — every positive linear functional on a Banach lattice is continuous
-- statement:
--   Let $\mathcal X$ be a **Banach lattice**: a real Banach space with a lattice order compatible with addition, such that $|X_1|\le|X_2|$ implies $\|X_1\|\le\|X_2\|$. If $l:\mathcal X\to\mathbb R$ is a linear functional which is positive, i.e.
--   $$l(X)\ge0\qquad\text{for all }X\succeq0,$$
--   then $l$ is continuous.
--
--   The proof of Proposition 3.1 cites this automatic-continuity theorem to upgrade an algebraic subgradient to a subgradient in $\mathcal X^*$.
--
--   **Formalization Note** A Banach lattice is encoded with Mathlib's classes `NormedAddCommGroup`, `NormedSpace ℝ`, `CompleteSpace`, `Lattice`, `HasSolidNorm` (the solidity condition $|X_1|\le|X_2|\Rightarrow\|X_1\|\le\|X_2\|$) and `IsOrderedAddMonoid` (order compatible with addition). These are exactly the conditions of the paper's definition on p. 437; compatibility of the order with multiplication by nonnegative scalars is not assumed, because it follows from them. Completeness and solidity are both needed.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 437, proof of Proposition 3.1: "by Levin [11, Theorem 0.12], we have that any positive linear functional on the Banach lattice 𝒳 is continuous"; Banach lattice defined on p. 437

import Mathlib
import Definitions.Def_ConvexRiskFn_Cont_Setting
open Filter Topology

namespace ConvexRiskFn.Cont

theorem positive_functional_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
    (l : E →ₗ[ℝ] ℝ) (hl : ∀ X : E, 0 ≤ X → 0 ≤ l X) :
    Continuous l := by sorry

end ConvexRiskFn.Cont
