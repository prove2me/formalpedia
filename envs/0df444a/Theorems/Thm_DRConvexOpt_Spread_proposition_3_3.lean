-- Prove2me | Theorems.Thm_DRConvexOpt_Spread_proposition_3_3
-- name    : DRConvexOpt.Spread.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:40:11.500982+00:00
-- url     : https://prove2.me/theorems/a21f7434-78e5-43f2-a679-ab985d51e736
-- title:
--   Proposition 3, assertion 3, p. 21 — an expected Huber loss bound E_Q[H_δ(fᵀz̃)] ≤ g is exactly Π_z̃𝒫 for a lifted set on ℝ^P × ℝ⁵₊
-- statement:
--   Let $f\in\mathbb R^P$, $\delta>0$ and $g\ge0$, let $H_\delta$ be the Huber loss (8), and let $\mathcal P$ be the set of probability distributions of $(\tilde z,\tilde u,\tilde v,\tilde w,\tilde s,\tilde t)$ on $\mathbb R^P\times\mathbb R^5_+$ with $\mathbb E_{\mathbb P}[\tilde w]=g$ and, almost surely,
--
--   $$
--   \delta(\tilde u-\tilde s)+\frac{\tilde s^2}{2}+\delta(\tilde v-\tilde t)+\frac{\tilde t^2}{2}\le\tilde w,\qquad \tilde u\ge\tilde s,\quad\tilde v\ge\tilde t,\quad f^\top\tilde z=\tilde u-\tilde v .
--   $$
--
--   Then
--
--   $$
--   \Pi_{\tilde z}\mathcal P=\big\{\mathbb Q\in\mathcal P_0(\mathbb R^P):\ \mathbb E_{\mathbb Q}[H_\delta(f^\top\tilde z)]\le g\big\}.
--   $$
--
--   In particular any $\mathbb Q^0$ with $\mathbb E_{\mathbb Q^0}[H_\delta(f^\top\tilde z)]\le g$ lies in $\Pi_{\tilde z}\mathcal P$, so a bound on an expected Huber loss is expressible within the standardized ambiguity set (4).
--
--   **Formalization Note** The page prints $\mathbb E_{\mathbb Q}[H_\delta(t^\top\tilde z)]\le g$ in the conclusion; no $t$ occurs in the proposition, its hypothesis and its proof (pp. 41–42) use $f^\top\tilde z$, so the statement uses $f^\top\tilde z$. The target set requires $H_\delta(f^\top\tilde z)$ to be $\mathbb Q$-integrable and the lifted set requires $\tilde w$ to be integrable (the expectations the page writes exist). The set identity is stated; the membership of $\mathbb Q^0$ is its immediate consequence. Auxiliary components $0,\dots,4$ are $\tilde u,\tilde v,\tilde w,\tilde s,\tilde t$.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 21, Proposition 3, assertion 3 (proof pp. 41–42)

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_huber
import Definitions.Def_DRConvexOpt_Spread_Huber

namespace DRConvexOpt.Spread

open MeasureTheory

/-- Proposition 3, assertion 3 (Expected Huber Loss Function), p. 21, with `fᵀz̃` for the printed
`tᵀz̃`: for `f ∈ ℝ^P`, `δ > 0` and `g ≥ 0`, the `z̃`-marginals of the lifted set `𝒫` are exactly the
distributions `Q` with `E_Q[H_δ(fᵀz̃)] ≤ g`. -/
theorem proposition_3_3 {nP : ℕ} (f : Fin nP → ℝ) (δ g : ℝ) (hδ : 0 < δ) (hg : 0 ≤ g) :
    huberSet f δ g = (fun μ => μ.map Prod.fst) '' liftedHuberSet f δ g := by sorry

end DRConvexOpt.Spread
