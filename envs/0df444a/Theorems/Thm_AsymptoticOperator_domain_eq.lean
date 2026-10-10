-- Prove2me | Theorems.Thm_AsymptoticOperator_domain_eq
-- name    : AsymptoticOperator.domain_eq
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T14:31:52.761986+00:00
-- url     : https://prove2.me/theorems/fd81522e-706f-49a9-84b1-9a069bdaf962
-- title:
--   The domain of the asymptotic operator is $W^{1,2}(S^1,\mathbb{R}^{2n})$ and is dense
-- statement:
--   Let $S:S^1\to\mathbb{R}^{2n\times2n}$ be continuous. A vector $f\in L^2(S^1,\mathbb{R}^{2n})$ lies in the domain of $A_S$ if and only if $\sum_{k\in\mathbb{Z}}(1+k^2)|\hat f_k|^2<\infty$. The domain is dense in $L^2(S^1,\mathbb{R}^{2n})$.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.2, p. 46; Hofer-Wysocki-Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995) 270-328, https://doi.org/10.1007/BF01895669, Section 3, p. 285, equation (35) (n = 1)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- Wendl §3.2: the domain of `A_S` is `W^{1,2}(S¹, ℝ²ⁿ)`, which is dense in `L²`. -/
theorem domain_eq {n : ℕ} (S : C(UnitAddCircle, Mat n)) :
    (∀ f : L2 n, f ∈ (asymptoticOperator S).domain ↔ InW12 f) ∧
      Dense ((asymptoticOperator S).domain : Set (L2 n)) := by sorry

end AsymptoticOperator
