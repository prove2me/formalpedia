-- Prove2me | Theorems.Thm_DROOptimal_Prescriptor_proposition_4
-- name    : DROOptimal.Prescriptor.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:13:18.583982+00:00
-- url     : https://prove2.me/theorems/57ad66a5-32f9-4985-998b-e55e8e9842b1
-- title:
--   Proposition 4, p. 20 — for r ≥ 0 there is a quasi-continuous selector x̂_r of arg min_{x∈X} ĉ_r(x,·)
-- statement:
--   Assume the standing assumptions of §2: $X\subseteq\mathbb R^n$ is compact (and non-empty), $\Xi=\{1,\dots,d\}$ is finite, and the cost $\gamma(x,i)$ is continuous in $x$ for every $i\in\Xi$. Let $\hat c_r$ be the distributionally robust predictor
--   $$
--   \hat c_r(x,\mathbb P')=\sup_{\mathbb P\in\mathcal P}\{c(x,\mathbb P): I(\mathbb P',\mathbb P)\le r\}.
--   $$
--   If $r\ge0$, then there is a quasi-continuous function $\hat x_r:\mathcal P\to X$ with
--   $$
--   \hat x_r(\mathbb P')\in\arg\min_{x\in X}\hat c_r(x,\mathbb P')\qquad\forall\,\mathbb P'\in\mathcal P. \tag{18}
--   $$
--
--   This shows that the distributionally robust prescriptor of Definition 7 exists, so that the pair $(\hat c_r,\hat x_r)$ belongs to the family $\mathcal X$ of data-driven predictor–prescriptor pairs.
--
--   **Formalization Note** The proposition prints "quasi-continuous data-driven predictor $\hat x_r$"; it is a prescriptor, a map $\mathcal P\to X$. The hypothesis that $X$ is non-empty is added: no function from the non-empty set $\mathcal P$ into an empty $X$ exists, and the paper's arg min (Definition 1) is implicitly over a non-empty $X$.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 20, Proposition 4 (with Definition 7, (18), p. 19)

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Prescriptor_Pairs

namespace DROOptimal.Prescriptor

/-- Proposition 4 (Quasi-continuity of x̂_r), p. 20: under the standing assumptions of §2 (p. 5) and
for r ≥ 0, there is a quasi-continuous x̂_r : 𝒫 → X with x̂_r(ℙ′) ∈ arg min_{x ∈ X} ĉ_r(x, ℙ′) for all
ℙ′ ∈ 𝒫 (18). The hypothesis `X.Nonempty` is pinned: no function into an empty X exists. -/
theorem proposition_4 {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (hXne : X.Nonempty) (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ xr : DROOptimal.Predictor.Δ d → ↥X, QuasiContinuous xr ∧ IsArgminSelector (DROOptimal.Predictor.drPredictor γ r) xr := by sorry

end DROOptimal.Prescriptor
