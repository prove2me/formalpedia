-- Prove2me | Theorems.Thm_CompOT_NotHilbertian_prop_8_2_not_negdef
-- name    : CompOT.NotHilbertian.prop_8_2_not_negdef
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:29.429404+00:00
-- url     : https://prove2.me/theorems/3b9a2725-1194-4832-ab57-f6047d0ca001
-- title:
--   §8.3, p. 507 — for d ≥ 2 and p = 1, 2 the squared p-Wasserstein distance on ℝ^d is not negative definite
-- statement:
--   Let $d\ge2$ and $p\in\{1,2\}$, and equip $\mathbb R^d$ with the Euclidean distance $\|x-y\|_2$. On the set $\mathcal P_p(\mathbb R^d)$ of probability measures with finite $p$-th moment, the squared Wasserstein distance $\mathcal W_p^2$ is **not** negative definite: there are $n$, measures $\mu_1,\dots,\mu_n\in\mathcal P_p(\mathbb R^d)$ and $r\in\mathbb R^n$ with $\sum_i r_i=0$ such that
--   $$\sum_{i,j=1}^n r_ir_j\,\mathcal W_p^2(\mu_i,\mu_j)>0.$$
--
--   By Proposition 8.1 (proved direction) this is what the book shows in order to conclude that $\mathcal W_p$ is not Hilbertian.
--
--   **Formalization Note** Negative definiteness is the zero-sum form of Definition 8.3, including symmetry ($\mathcal W_p^2$ is symmetric, so the failure is in the inequality). The distance is the published `wassersteinDistance` on `EuclideanSpace ℝ (Fin d)`, real-valued on $\mathcal P_p(\mathbb R^d)$.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §8.3, sentence before Proposition 8.2, p. 507

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_CompOT_NotHilbertian_Defs

namespace CompOT.NotHilbertian

/-- p. 507, sentence before Proposition 8.2: the squared `p`-Wasserstein distance on
`ℝ^d` (`d ≥ 2`, ground distance `‖x - y‖₂`, probability measures with finite `p`-th
moment) is not negative definite, for `p = 1, 2`. -/
theorem prop_8_2_not_negdef (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : p = 1 ∨ p = 2) :
    ¬ IsCondNegDef (fun μ ν : Pp d p => Wp d p μ ν ^ 2) := by sorry

end CompOT.NotHilbertian
