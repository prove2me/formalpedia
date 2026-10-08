-- Prove2me | Theorems.Thm_BSUMConv_BSCA_theorem_4
-- name    : BSUMConv.BSCA.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:05.453557+00:00
-- url     : https://prove2.me/theorems/6529f016-ee4c-4b7d-a8c9-ed21cd8703ae
-- title:
--   Theorem 4, p. 18 — every BSCA limit point is stationary
-- statement:
--   Let $X=\prod_{i=1}^{N}X_i$ with each $X_i$ nonempty, closed and convex. Let $f$ be continuously differentiable, and let each block approximation $h_i$ agree with $f$ to first order, be strictly convex in its trial block, and be continuous in the trial block and base point. For every cyclic BSCA run using the largest Armijo-admissible step from $\{\alpha^{\rm init}\beta^j:j\ge0\}$, where $0<\sigma,\beta<1$ and $0<\alpha^{\rm init}\le1$, every limit point $z$ of the iterates is stationary for the constrained problem:
--   $$f'(z;d)\ge0\qquad\text{whenever }z+d\in X.$$
--
--   The result identifies the possible accumulation points of the algorithm without assuming that the entire sequence converges.
--
--   **Formalization Note** The additional bound $\alpha^{\rm init}\le1$ ensures all iterates stay in $X$. Figure 4's mixed iteration indices are resolved according to the adjacent text and proof. Stationarity uses the published extended-real lower directional derivative of $f$ extended by $+\infty$ outside $X$; for $C^1$ functions on a convex feasible set it gives the displayed feasible-direction condition. The block product has the sup norm, which leaves convergence and stationarity unchanged in finite dimension.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, p. 18, Theorem 4 (with §II p. 4, §IV p. 8, Fig. 4 p. 17)

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSCA_Setting

namespace BSUMConv.BSCA

open Filter Topology TsengBCD.Stationary

/-- Theorem 4, p. 18: every limit point of cyclic BSCA is stationary for (12). -/
theorem theorem_4 {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (f : X n → ℝ)
    (h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ)
    (s : ℕ → Fin N) (σ β αinit : ℝ) (x y : ℕ → X n) (j : ℕ → ℕ)
    (hclosed : ∀ i, IsClosed (Xs i)) (hconvXs : ∀ i, Convex ℝ (Xs i))
    (hnonempty : ∀ i, (Xs i).Nonempty)
    (hC1 : ContDiff ℝ 1 f) (hmatch : FirstOrderAgreement Xs f h)
    (hstrict : StrictApprox Xs h) (hcont : ContinuousApprox Xs h)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 < αinit) (hα1 : αinit ≤ 1)
    (hcyclic : IsCyclic s) (hrun : IsBSCARun Xs f h s σ β αinit x y j) :
    ∀ z : X n, MapClusterPt z atTop x → IsStationary (fext f (BSUMConv.BSUM.Xset Xs)) z := by sorry

end BSUMConv.BSCA
