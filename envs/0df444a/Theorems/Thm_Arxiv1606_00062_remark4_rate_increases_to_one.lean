-- Prove2me | Theorems.Thm_Arxiv1606_00062_remark4_rate_increases_to_one
-- name    : Arxiv1606_00062.remark4_rate_increases_to_one
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T22:13:41.294106+00:00
-- url     : https://prove2.me/theorems/871efe68-6220-4266-b4ed-21287a0da1c2
-- title:
--   Remark 4: $|\mathcal R_2|$ increases to $1$ as the distance between the obstacles decreases to zero
-- statement:
--   Let $k>0$ be the wavenumber, and let $\kappa_1,\kappa_2>0$ be the curvatures of two smooth strictly convex obstacles in the plane at the points $a_1,a_2$ realising their distance $d=|a_1-a_2|>0$. Let $\mathcal R_2(d)$ be the two-dimensional rate of Theorem 3,
--
--   $$\mathcal R_2(d)=e^{2ikd}\Big(\sqrt{(1+d\kappa_1)(1+d\kappa_2)}\,\Big[1+\sqrt{1-[(1+d\kappa_1)(1+d\kappa_2)]^{-1}}\Big]\Big)^{-1}.$$
--
--   Then $d\mapsto|\mathcal R_2(d)|$ is strictly decreasing on $(0,\infty)$, and
--
--   $$\lim_{d\to0^+}|\mathcal R_2(d)|=1.$$
--
--   So as the distance between the obstacles decreases to zero, $|\mathcal R_2|$ increases to $1$, and the geometric convergence of the Neumann series deteriorates.
--
--   **Formalization Note** Only the second sentence of Remark 4 is stated. The first sentence, $\eta\sim\sum_{m\le M}\eta^m+(\eta^{M+1}+\eta^{M+2})\sum_m\mathcal R_2^m$ for $M\gg\log k$, uses an undefined asymptotic relation and is not stated. The distance $d$ varies with the curvatures $\kappa_1,\kappa_2$ held fixed (for example, one obstacle translated along the line through $a_1$ and $a_2$). Strict convexity is read as positive curvature; if $\kappa_1=\kappa_2=0$ then $|\mathcal R_2|=1$ for every $d$.
-- source:
--   Boubendir, Ecevit and Reitich, Acceleration of an iterative method for the evaluation of high-frequency multiple scattering effects, arXiv:1606.00062v1 (2016), claim c018; Section 3, Remark 4 (second sentence), with the two-dimensional formula for R_2 of Theorem 3, PDF p. 7

import Mathlib
import Definitions.Def_Arxiv1606_00062_Basic

open Filter Topology

namespace Arxiv1606_00062

theorem remark4_rate_increases_to_one (k κ₁ κ₂ : ℝ) (hk : 0 < k) (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) :
    StrictAntiOn (fun d : ℝ => ‖rateR2 k d κ₁ κ₂‖) (Set.Ioi 0) ∧
    Tendsto (fun d : ℝ => ‖rateR2 k d κ₁ κ₂‖) (𝓝[>] 0) (𝓝 1) := by sorry

end Arxiv1606_00062
