-- Prove2me | Theorems.Thm_CompOT_NotHilbertian_prop_8_2_reduction
-- name    : CompOT.NotHilbertian.prop_8_2_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:05.591781+00:00
-- url     : https://prove2.me/theorems/1c1911f0-46d2-41db-a198-0d6be8709133
-- title:
--   Proof of Proposition 8.2, p. 507 — a counterexample in ℝ² gives one in ℝ^d for every d ≥ 2
-- statement:
--   Let $d\ge2$ and $p\in\{1,2\}$. If the squared $p$-Wasserstein distance $\mathcal W_p^2$ on $\mathcal P_p(\mathbb R^d)$ (Euclidean ground distance) were negative definite, then the squared $p$-Wasserstein distance on $\mathcal P_p(\mathbb R^2)$ would be negative definite as well. Equivalently: every $n$, $\mu_1,\dots,\mu_n\in\mathcal P_p(\mathbb R^2)$ and zero-sum $r$ with
--   $$\sum_{i,j}r_ir_j\,\mathcal W_p^2(\mu_i,\mu_j)>0$$
--   yield measures on $\mathbb R^d$ with the same property.
--
--   This is the first step of the proof of Proposition 8.2: it reduces the claim to the plane.
--
--   **Formalization Note** Negative definiteness is the zero-sum form of Definition 8.3.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), proof of Proposition 8.2, first sentence, p. 507

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_CompOT_NotHilbertian_Defs

namespace CompOT.NotHilbertian

/-- Proof of Proposition 8.2, p. 507: "any counterexample in dimension 2 suffices to obtain a
counterexample in any higher dimension". If the squared `p`-Wasserstein distance on
`ℝ^d` with `d ≥ 2` and `p = 1` or `p = 2` were negative definite, so would be the squared `p`-Wasserstein
distance on `ℝ²`. -/
theorem prop_8_2_reduction (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : p = 1 ∨ p = 2) :
    IsCondNegDef (fun μ ν : Pp d p => Wp d p μ ν ^ 2) →
      IsCondNegDef (fun μ ν : Pp 2 p => Wp 2 p μ ν ^ 2) := by sorry

end CompOT.NotHilbertian
