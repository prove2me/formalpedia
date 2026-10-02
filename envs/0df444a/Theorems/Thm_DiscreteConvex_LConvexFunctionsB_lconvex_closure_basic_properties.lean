-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsB_lconvex_closure_basic_properties
-- name    : DiscreteConvex.LConvexFunctionsB.lconvex_closure_basic_properties
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:28:19.756182+00:00
-- url     : https://prove2.me/theorems/3f7952c5-7d16-4d82-b179-780938807159
-- title:
--   Theorem 7.19 -- lconvex_closure_basic_properties
-- statement:
--   **Theorem 7.19** (p.187-188), parts (3)-(4). Let $g\in L[\mathbb Z\to\mathbb R]$ be L-convex with convex closure $\bar g$. (3) $\bar g(p)=g(p)$ for $p\in\mathbb Z^V$. (4) $\bar g(q+\alpha\mathbf 1)=\bar g(q)+\alpha r$ for $q\in\mathbb R^V$, $\alpha\in\mathbb R$, with the constant $r$ of (TRF[Z]).
--
--   **Formalization Note.** Parts (1), (2), and (5) — the explicit Lov\'asz-extension-formula construction of $\bar g$ on $[p,p+1]_{\mathbb R}$ via the sorted distinct components of $q$ — are not restated here: no other result in this mission needs the specific piecewise-linear formula, only the two structural facts (3)-(4) that any convex closure agreeing with $g$ on $\mathbb Z^V$ and inheriting its translation constant must satisfy. See `HARD.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.187-188, Theorem 7.19.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.187-188, Theorem 7.19

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_ConvexClosureVal

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.19 (p.187-188), parts (3)-(4). The convex closure of an L-convex function agrees
with `g` on `Zⱽ` and inherits its translation constant `r`. -/
theorem lconvex_closure_basic_properties (g : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g) :
    (∀ p : V → ℤ, ConvexClosureVal g (fun v => (p v : ℝ)) = g p) ∧
    (∃ r : ℝ, (∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)) ∧
      ∀ q : V → ℝ, ∀ alpha : ℝ,
        ConvexClosureVal g (fun v => q v + alpha) = ConvexClosureVal g q + (alpha * r : WithTop ℝ)) := by sorry

end DiscreteConvex.LConvexFunctionsB
