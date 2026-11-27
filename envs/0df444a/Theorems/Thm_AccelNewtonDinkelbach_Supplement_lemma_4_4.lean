-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_Supplement_lemma_4_4
-- name    : AccelNewtonDinkelbach.Supplement.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:03:36.59277+00:00
-- url     : https://prove2.me/theorems/e51ccd3f-7d4d-5687-ba77-9123dcc05c33
-- title:
--   Lemma 4.4 — either parametric failure test makes $(F_u)$ unbounded
-- statement:
--   Let $x$ be feasible for $(F_u)$ and $\bar\delta=c^\top x/(1-\sum_{e\in\delta^-(u)}\gamma_ex_e)$. If $f(\bar\delta)=-\infty$, or if this value is attained at some $\bar x\in D$ with nonpositive denominator and is strictly negative, then the value of $(F_u)$ is $-\infty$.
--
--   Differences from the source:
--   - generalization: the full graph G → an arbitrary selected arc subgraph A; reason: taking every arc recovers the source, and the same definitions and claim apply to each phase subgraph G^(k)
--   - encoding: extended-real unbounded values → EReal equality to ⊥; reason: avoids a total real infimum returning a junk value
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 4.4, p.12

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_Supplement_M2VPIFractional

namespace AccelNewtonDinkelbach.Supplement

set_option autoImplicit false

/-- **Lemma 4.4 (unboundedness test for `(F_u)`).**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 4.4, p.12. -/
theorem lemma_4_4 {n m : ℕ} (M : M2VPI n m) (A : Fin m → Prop) (u : Fin n)
    (x : Fin m → ℝ) (hx : M.FuFeasible A u x)
    (δbar : ℝ) (hδbar : δbar = M.flowCost A x / M.denominator A u x)
    (htest : M.paramF A u δbar = ⊥ ∨
      ∃ xbar : Fin m → ℝ, M.InD A u xbar ∧ M.denominator A u xbar ≤ 0 ∧
        M.paramF A u δbar =
          ((M.flowCost A xbar - δbar * M.denominator A u xbar : ℝ) : EReal) ∧
        M.flowCost A xbar - δbar * M.denominator A u xbar < 0) :
    M.fuValue A u = ⊥ := by sorry

end AccelNewtonDinkelbach.Supplement
