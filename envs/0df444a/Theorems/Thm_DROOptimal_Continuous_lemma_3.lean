-- Prove2me | Theorems.Thm_DROOptimal_Continuous_lemma_3
-- name    : DROOptimal.Continuous.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:25.307403+00:00
-- url     : https://prove2.me/theorems/0bdfacd4-e718-4ffc-8226-21f3f07447ab
-- title:
--   Lemma 3, p. 31 — for r > 0, ϵ ≥ 0: ĉ_r ≤ ĉ_{r,ϵ} ≤ ĉ_r + ϵ on X × 𝒫
-- statement:
--   Throughout, $X\subseteq\mathbb R^n$ and $\Xi\subseteq\mathbb R^d$ are compact, $\gamma:X\times\Xi\to\mathbb R$ is jointly continuous (the standing assumptions of §2, p. 5, and §5, p. 23), and $\mathcal P$ is the set of Borel probability distributions on $\Xi$ with the topology of weak convergence. Let $\hat c_r$ be the distributionally robust predictor and $\hat c_{r,\epsilon}$ the predictor defined by problem (34).
--
--   **Lemma 3 (Uniform approximation of $\hat c_r$).** If $r>0$ and $\epsilon\ge0$, then
--   $$
--   \hat c_r(x,\mathbb P')\le\hat c_{r,\epsilon}(x,\mathbb P')\le\hat c_r(x,\mathbb P')+\epsilon\qquad\forall x\in X,\ \mathbb P'\in\mathcal P.
--   $$
--
--   So $\hat c_{r,\epsilon}\to\hat c_r$ uniformly as $\epsilon\downarrow0$, which transfers continuity from $\hat c_{r,\epsilon}$ to $\hat c_r$ in Proposition 6.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 31, Lemma 3

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting
import Definitions.Def_DROOptimal_Continuous_Appendix

namespace DROOptimal.Continuous

/-- Lemma 3 (p. 31): for `r > 0` and `ϵ ≥ 0`, `ĉ_r ≤ ĉ_{r,ϵ} ≤ ĉ_r + ϵ` on `X × 𝒫`. -/
theorem lemma_3 {d n : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : IsCompact X) (hΞ : IsCompact Ξ) (γ : ↥X → ↥Ξ → ℝ)
    (hγ : Continuous (fun p : ↥X × ↥Ξ => γ p.1 p.2)) (r ε : ℝ) (hr : 0 < r) (hε : 0 ≤ ε) :
    ∀ (x : ↥X) (ℙ' : Dist Ξ),
      drPredictor γ r x ℙ' ≤ acPredictor γ r ε x ℙ' ∧
        acPredictor γ r ε x ℙ' ≤ drPredictor γ r x ℙ' + ε := by sorry

end DROOptimal.Continuous
