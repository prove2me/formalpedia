-- Prove2me | Theorems.Thm_CompOT_NotHilbertian_remark_2_13_discrete
-- name    : CompOT.NotHilbertian.remark_2_13_discrete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:18.812134+00:00
-- url     : https://prove2.me/theorems/40373e50-ae09-4f21-b0af-8149af7b183c
-- title:
--   Remark 2.13, p. 375 — between discrete measures on common points, W_p(α, β)^p equals the discrete cost L_C(a, b), C_{i,j} = ‖x_i − x_j‖^p
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$, let $a,b\in\Sigma_n$ be histograms (nonnegative, summing to $1$), and let $p\ge1$. Put $\alpha=\sum_ia_i\delta_{x_i}$ and $\beta=\sum_jb_j\delta_{x_j}$, and let $C$ be the $n\times n$ matrix $C_{i,j}=\|x_i-x_j\|_2^p$. Then
--   $$\mathcal W_p(\alpha,\beta)^p=L_C(a,b)=\min_{P\in U(a,b)}\sum_{i,j}C_{i,j}P_{i,j}.$$
--
--   Remark 2.13 says that the discrete Kantorovich problem is the special case of the problem between measures obtained by restricting to couplings $\pi=\sum_{i,j}P_{i,j}\delta_{(x_i,x_j)}$; this identity is that statement for the $p$-Wasserstein cost. It is what turns the distances between the 35 measures of the proof of Proposition 8.2 into finite linear programs.
--
--   **Formalization Note** $\mathcal W_p$ is the published `wassersteinDistance` (an infimum over all measures on $\mathbb R^d\times\mathbb R^d$ with marginals $\alpha,\beta$), converted to a real number; it is finite here. The points need not be distinct. $L_C$ is a real infimum over $U(a,b)$, which is nonempty for $a,b\in\Sigma_n$.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Remark 2.13, p. 375, with (2.11), p. 371 and (2.18), p. 377

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_CompOT_NotHilbertian_Defs

namespace CompOT.NotHilbertian

/-- Remark 2.13, p. 375: between the discrete measures `α = ∑ᵢ aᵢ δ_{xᵢ}` and
`β = ∑ⱼ bⱼ δ_{xⱼ}` on `ℝ^d` (`a, b ∈ Σₙ`), the Kantorovich problem over CompOT.W1.couplings of
measures reduces to the discrete one over `π = ∑_{i,j} P_{i,j} δ_{(xᵢ,xⱼ)}`, `P ∈ U(a, b)`:
`W_p(α, β)^p = L_C(a, b)` with `C_{i,j} = ‖xᵢ - xⱼ‖^p`. -/
theorem remark_2_13_discrete {d n : ℕ} (x : Fin n → E d) (a b : Fin n → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n)) (p : ℝ) (hp : 1 ≤ p) :
    wp p (discreteMeasure x a) (discreteMeasure x b) ^ p =
      otCost (Matrix.of fun i j => ‖x i - x j‖ ^ p) a b := by sorry

end CompOT.NotHilbertian
