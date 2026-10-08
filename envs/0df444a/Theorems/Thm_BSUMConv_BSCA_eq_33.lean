-- Prove2me | Theorems.Thm_BSUMConv_BSCA_eq_33
-- name    : BSUMConv.BSCA.eq_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:43.449771+00:00
-- url     : https://prove2.me/theorems/9ca9c058-5551-4405-8a20-84824e34bd99
-- title:
--   (33), p. 18 — scaled directional derivatives vanish
-- statement:
--   Consider a BSCA run with Armijo parameters $0<\sigma,\beta<1$ and $0<\alpha^{\rm init}\le1$. Assume the objective is continuously differentiable, the block approximations agree to first order and are convex, and the iterate sequence has a limit point. With $d^r=y^r-x^r$ and $\alpha^r=\alpha^{\rm init}\beta^{j_r}$,
--   $$\lim_{r\to\infty}\alpha^r f'(x^r;d^r)=0.$$
--
--   This gives the vanishing quantity used in the two-case limit-point analysis.
--
--   **Formalization Note** The existence of a limit point makes explicit the proof's standing situation; it supplies a lower bound on the decreasing objective values. The restriction $\alpha^{\rm init}\le1$ ensures feasible trial points.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, p. 18, (33)

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSCA_Setting

namespace BSUMConv.BSCA

open Filter Topology TsengBCD.Stationary

/-- Display (33), p. 18: the scaled directional derivative tends to zero when the
monotone objective has a limit point. -/
theorem eq_33 {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (f : X n → ℝ)
    (h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ)
    (s : ℕ → Fin N) (σ β αinit : ℝ) (x y : ℕ → X n) (j : ℕ → ℕ)
    (hC1 : ContDiff ℝ 1 f)
    (hmatch : FirstOrderAgreement Xs f h)
    (hconvXs : ∀ i, Convex ℝ (Xs i))
    (hconvH : ∀ i z, z ∈ BSUMConv.BSUM.Xset Xs → ConvexOn ℝ (Xs i) (fun xi => h i xi z))
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 < αinit) (hα1 : αinit ≤ 1)
    (hrun : IsBSCARun Xs f h s σ β αinit x y j)
    (z : X n) (hcluster : MapClusterPt z atTop x) :
    Tendsto (fun r => (αinit * β ^ (j r)) *
      fderiv ℝ f (x r) (y r - x r)) atTop (𝓝 0) := by sorry

end BSUMConv.BSCA
