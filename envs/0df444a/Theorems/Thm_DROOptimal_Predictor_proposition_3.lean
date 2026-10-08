-- Prove2me | Theorems.Thm_DROOptimal_Predictor_proposition_3
-- name    : DROOptimal.Predictor.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:50.093334+00:00
-- url     : https://prove2.me/theorems/cc24ba08-4d8e-46f5-83dd-c43a2f6310be
-- title:
--   Proposition 3, p. 16 — for r ≥ 0 the distributionally robust predictor ĉ_r is continuous on X × 𝒫
-- statement:
--   Let $X\subseteq\mathbb R^n$ be compact, $\Xi=\{1,\dots,d\}$, $\gamma:X\times\Xi\to\mathbb R$ continuous in $x$ for each $i$, and let
--   $$
--   \hat c_r(x,\mathbb P')=\sup_{\mathbb P\in\mathcal P}\{c(x,\mathbb P): I(\mathbb P',\mathbb P)\le r\}
--   $$
--   be the distributionally robust predictor (10). If $r\ge0$, then $\hat c_r$ is (jointly) continuous on $X\times\mathcal P$; that is, $\hat c_r$ belongs to the class $\mathcal C$ of data-driven predictors.
--
--   Continuity is half of feasibility in (5) and is needed for $\hat c_r$ to be a competitor at all.
--
--   **Formalization Note** Continuity is with respect to the product of the subspace topologies on $X$ and on the simplex $\mathcal P$.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 16, Proposition 3 (and Remark 2, p. 15, for r = 0)

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

namespace DROOptimal.Predictor

/-- Proposition 3 (Continuity of ĉ_r), p. 16: under the standing assumptions of §2 (p. 5), if r ≥ 0
then the distributionally robust predictor ĉ_r is continuous on X × 𝒫. -/
theorem proposition_3 {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 ≤ r) :
    IsPredictor (drPredictor γ r) := by sorry

end DROOptimal.Predictor
