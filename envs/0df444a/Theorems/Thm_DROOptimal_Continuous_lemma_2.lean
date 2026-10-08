-- Prove2me | Theorems.Thm_DROOptimal_Continuous_lemma_2
-- name    : DROOptimal.Continuous.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:36.307026+00:00
-- url     : https://prove2.me/theorems/22604a7d-068f-4a1f-b093-54f9f6a13055
-- title:
--   Lemma 2 (33), p. 29 — for r ≥ 0, ĉ_r equals the absolutely continuous representation (33)
-- statement:
--   Throughout, $X\subseteq\mathbb R^n$ and $\Xi\subseteq\mathbb R^d$ are compact, $\gamma:X\times\Xi\to\mathbb R$ is jointly continuous (the standing assumptions of §2, p. 5, and §5, p. 23), and $\mathcal P$ is the set of Borel probability distributions on $\Xi$ with the topology of weak convergence. Let $I$ be the relative entropy of Definition 8, $\hat c_r(x,\mathbb P')=\sup\{c(x,\mathbb P):\mathbb P\in\mathcal P,\ I(\mathbb P',\mathbb P)\le r\}$, and $\bar\gamma(x)=\max_{\xi\in\Xi}\gamma(x,\xi)$.
--
--   **Lemma 2 (Absolutely continuous representation of $\hat c_r$).** If $r\ge0$, then for every $x\in X$ and $\mathbb P'\in\mathcal P$,
--   $$
--   \hat c_r(x,\mathbb P')=\sup_{\substack{\mathbb P_c\in\mathcal P\\ p\in[0,1]}}\Big\{p\cdot\int_\Xi\gamma(x,\xi)\,\mathrm d\mathbb P_c(\xi)+(1-p)\cdot\bar\gamma(x)\ :\ \mathbb P'\ll p\cdot\mathbb P_c\ll\mathbb P',\ \int_\Xi\log\Big(\frac1p\cdot\frac{\mathrm d\mathbb P'}{\mathrm d\mathbb P_c}(\xi)\Big)\mathrm d\mathbb P'(\xi)\le r\Big\}.
--   $$
--
--   The worst-case distribution may put mass outside the support of $\mathbb P'$ only on the worst-case scenarios $\arg\max_\xi\gamma(x,\xi)$; the lemma makes this explicit, and is the first step of the paper's dual representation of $\hat c_r$.
--
--   **Formalization Note** The right-hand side is the predictor $\hat c_{r,\epsilon}$ of (34) at $\epsilon=0$, as defined in the Appendix module, whose integral constraint includes integrability of the integrand.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 29, Lemma 2, (33); proof pp. 29–31

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting
import Definitions.Def_DROOptimal_Continuous_Appendix

namespace DROOptimal.Continuous

/-- Lemma 2 (p. 29): for `r ≥ 0`, `ĉ_r` equals the optimal value of (33), which is (34) at `ϵ = 0`. -/
theorem lemma_2 {d n : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : IsCompact X) (hΞ : IsCompact Ξ) (γ : ↥X → ↥Ξ → ℝ)
    (hγ : Continuous (fun p : ↥X × ↥Ξ => γ p.1 p.2)) (r : ℝ) (hr : 0 ≤ r) (x : ↥X) (ℙ' : Dist Ξ) :
    drPredictor γ r x ℙ' = acPredictor γ r 0 x ℙ' := by sorry

end DROOptimal.Continuous
