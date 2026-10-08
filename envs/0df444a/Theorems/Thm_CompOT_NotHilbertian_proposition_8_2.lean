-- Prove2me | Theorems.Thm_CompOT_NotHilbertian_proposition_8_2
-- name    : CompOT.NotHilbertian.proposition_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:14.186975+00:00
-- url     : https://prove2.me/theorems/8ab0ad33-3862-4073-aa97-cfe5b4ba1508
-- title:
--   Proposition 8.2, p. 507 — for d ≥ 2 and p = 1, 2 the p-Wasserstein distance on ℝ^d is not Hilbertian
-- statement:
--   Let $\mathcal X=\mathbb R^d$ with $d\ge2$, with ground distance $d(x,y)=\|x-y\|_2$, and let $p\in\{1,2\}$. Let $\mathcal P_p(\mathbb R^d)$ be the probability measures on $\mathbb R^d$ with finite $p$-th moment and $\mathcal W_p$ the $p$-Wasserstein distance (2.18) on it. Then $\mathcal W_p$ is **not Hilbertian**: there is no real Hilbert space $\mathcal H$ and map $\phi:\mathcal P_p(\mathbb R^d)\to\mathcal H$ with
--   $$\mathcal W_p(\mu,\nu)=\|\phi(\mu)-\phi(\nu)\|_{\mathcal H}\qquad\text{for all }\mu,\nu\in\mathcal P_p(\mathbb R^d).$$
--
--   In dimension one $\mathcal W_2$ is Hilbertian (through quantile functions, Remark 2.30; in particular between univariate Gaussians, Remark 2.31); this proposition shows that such an isometric embedding is impossible from dimension two on, so the facts the book lists for Hilbertian distances (p. 506: positive definiteness of $e^{-d^p/t}$, low-distortion embeddings) cannot be obtained for $\mathcal W_p$ through an isometric embedding.
--
--   **Formalization Note** The Wasserstein distance is the published `WassersteinDRO.Duality.wassersteinDistance` on `EuclideanSpace ℝ (Fin d)`, as a real number; its domain is the set where it is finite, the probability measures with finite $p$-th moment (the book's statement names no domain). Since the counterexample uses finitely supported measures, the result also holds on any smaller set containing them. Hilbert spaces are real and lie in the universe of the domain.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 8.2, p. 507

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_CompOT_NotHilbertian_Defs

namespace CompOT.NotHilbertian

/-- Proposition 8.2, p. 507: if `X = ℝ^d` with `d ≥ 2` and the ground cost is
`d(x, y) = ‖x - y‖₂`, then the `p`-Wasserstein distance (on the probability measures with
finite `p`-th moment) is not Hilbertian for `p = 1, 2`. -/
theorem proposition_8_2 (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : p = 1 ∨ p = 2) :
    ¬ IsHilbertian (Wp d p) := by sorry

end CompOT.NotHilbertian
