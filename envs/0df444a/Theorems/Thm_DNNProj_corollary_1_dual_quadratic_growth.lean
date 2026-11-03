-- Prove2me | Theorems.Thm_DNNProj_corollary_1_dual_quadratic_growth
-- name    : DNNProj.corollary_1_dual_quadratic_growth
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:14.037119+00:00
-- url     : https://prove2.me/theorems/7ad33808-2c7d-408e-a2c2-de8d04618ae7
-- title:
--   Corollary 1 — quadratic growth of the dual (D) of the DNN projection at every dual solution when $\operatorname{rank}\bar X\ge n-1$ or a strictly complementary dual solution exists
-- statement:
--   Let $G\in\mathbb S^n$ and let $\bar X\in\mathrm{SOL_P}$ be the (unique) optimal solution of the DNN projection problem (P). Suppose one of the following two conditions holds:
--
--   1. $\operatorname{rank}(\bar X)\ge n-1$;
--   2. there exists $(\hat S,\hat Z)\in\mathrm{SOL_D}$ such that $\operatorname{rank}(\bar X)+\operatorname{rank}(\hat S)=n$.
--
--   Then the quadratic growth condition of (D) holds at **every** $(\bar S,\bar Z)\in\mathrm{SOL_D}$: there are $\kappa,\varepsilon>0$ with
--   $$\tfrac12\|S+Z+G\|^2\ge\tfrac12\|\bar S+\bar Z+G\|^2+\kappa\operatorname{dist}^2\big((S,Z),\mathrm{SOL_D}\big)$$
--   for all $S\in\mathbb S^n_+$, $Z\in\mathbb N^n$ with $\|(S,Z)-(\bar S,\bar Z)\|\le\varepsilon$.
--
--   Dual quadratic growth is the hypothesis under which the augmented Lagrangian method for (P) has an asymptotically superlinear KKT residual; the corollary supplies it even when (D) has many solutions.
--
--   **Formalization Note** Uniqueness of $\bar X$ is a fact (strong convexity), not a hypothesis. The rank condition (i) is compared in $\mathbb Z$.
--
--   Differences from the source:
--   - encoding: Sⁿ, Frobenius norm; Sⁿ × Sⁿ → SunNLSDP.Equiv.SymMat (Fin n); WithLp 2 (Sⁿ × Sⁿ) with ‖(S,Z)‖² = ‖S‖² + ‖Z‖²; reason: the inner-product space of the instance of (9) on p.11
--   - encoding: the quadratic growth condition of (D) (Definition 4 for the instance of (9) on p.11) → DualQuadGrowthAt: growth of ½‖S + Z + G‖² over feasible (S, Z) in a closed ball, distance to SOL_D; reason: θ = h∘ℱ + p equals ½‖S + Z + G‖² on the feasible set and +∞ off it; the constant −½‖G‖² and the outer sign of (D) cancel
--   - encoding: rank(X̄) ≥ n − 1 → (n : ℤ) − 1 ≤ rank X̄; reason: avoids natural-number subtraction at n = 0
-- source:
--   Cui, Liang, Sun, Toh, On Degenerate Doubly Nonnegative Projection Problems, arXiv:2009.11272v2 (preprint basis), https://arxiv.org/abs/2009.11272v2, Corollary 1, p.13

import Mathlib
import Definitions.Def_DNNProj_Basics
import Definitions.Def_DNNProj_DNN

open scoped RealInnerProductSpace

namespace DNNProj

/-- **Corollary 1** (Cui–Liang–Sun–Toh, arXiv:2009.11272v2, p.13). Let `X̄ ∈ SOL_P` be the unique
optimal solution of (P), the projection of `G ∈ Sⁿ` onto the doubly nonnegative cone. The
quadratic growth condition of (D) holds at any `(S̄, Z̄) ∈ SOL_D` under one of the following two
conditions:
(i) `rank(X̄) ≥ n − 1`;
(ii) there exists `(Ŝ, Ẑ) ∈ SOL_D` such that `rank(X̄) + rank(Ŝ) = n`.

**Formalization Note.** `Sⁿ` carries the Frobenius norm and `Sⁿ × Sⁿ` the Euclidean product norm.
The quadratic growth condition of (D) is Definition 4 for (D) viewed as the instance of (9) on
p.11 (`h(U) = ½‖U + G‖²`, `ℱ(S, Z) = S + Z`, `p = δ_{Sⁿ₊}(S) + δ_{Nⁿ}(Z)`): `DualQuadGrowthAt`.
Uniqueness of `X̄` is a fact (strong convexity), not a hypothesis. `rank(X̄) ≥ n − 1` is compared
in `ℤ`. The hypothesis is the disjunction (i) ∨ (ii). -/
theorem corollary_1_dual_quadratic_growth {n : ℕ} (G Xbar : Sym n) (hX : Xbar ∈ solPrimal G)
    (hcond : (n : ℤ) - 1 ≤ ((toMat Xbar).rank : ℤ) ∨
      ∃ q ∈ solDual G, (toMat Xbar).rank + (toMat q.fst).rank = n) :
    ∀ qbar ∈ solDual G, DualQuadGrowthAt G qbar := by sorry

end DNNProj
