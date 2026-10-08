-- Prove2me | Theorems.Thm_DROOptimal_Predictor_theorem_2
-- name    : DROOptimal.Predictor.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:54.999041+00:00
-- url     : https://prove2.me/theorems/879d6113-7fdb-4552-96bc-e48ae16195db
-- title:
--   Theorem 2 (Strong LDP), (9), p. 13 — ℙ^∞(ℙ̂_T ∈ 𝒟) ≤ (T+1)^d e^{−T inf_{ℙ′∈𝒟} I(ℙ′,ℙ)} for all T ≥ 1
-- statement:
--   Let $\xi_1,\xi_2,\dots$ be drawn independently from a distribution $\mathbb P$ on $\Xi=\{1,\dots,d\}$, and let $\hat{\mathbb P}_T$ be the empirical distribution of $\xi_1,\dots,\xi_T$. Then for every Borel set $\mathcal D\subseteq\mathcal P$ and every $T\ge1$,
--   $$
--   \mathbb P^\infty\big(\hat{\mathbb P}_T\in\mathcal D\big)\le (T+1)^d\,e^{-T\inf_{\mathbb P'\in\mathcal D}I(\mathbb P',\mathbb P)} ,
--   $$
--   where $I$ is the relative entropy and $e^{-\infty}=0$.
--
--   This is the finite-sample (method of types) form of Sanov's theorem; it gives the finite-sample guarantee of Theorem 5.
--
--   **Formalization Note** The infimum is taken in the extended reals (it is $+\infty$ for empty $\mathcal D$). The bound is stated for every real $s\le\inf_{\mathbb P'\in\mathcal D}I(\mathbb P',\mathbb P)$ as $\mathbb P^\infty(\hat{\mathbb P}_T\in\mathcal D)\le(T+1)^de^{-Ts}$; this is the displayed inequality when the infimum is finite, and forces probability $0$ when it is $+\infty$. Borel means `MeasurableSet D` in the simplex subtype. The paper writes $\forall T\in\mathbb N$; the empirical distribution is defined for $T\ge1$ only, so $T\ge1$ is assumed.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 13, Theorem 2, (9)

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

namespace DROOptimal.Predictor

/-- Theorem 2 (Strong LDP), (9), p. 13: if the samples are drawn independently from ℙ ∈ 𝒫, then for
every Borel set 𝒟 ⊆ 𝒫 and every T ≥ 1,
ℙ^∞(ℙ̂_T ∈ 𝒟) ≤ (T + 1)^d e^{−T inf_{ℙ′ ∈ 𝒟} I(ℙ′, ℙ)}.
The infimum lives in `EReal` (it is +∞ when 𝒟 is empty or I(·, ℙ) ≡ ∞ on 𝒟, and then the bound is 0);
the bound is stated for every real s ≤ inf_{ℙ′ ∈ 𝒟} I(ℙ′, ℙ). -/
theorem theorem_2 {d : ℕ} (ℙ : Δ d) (D : Set (Δ d)) (hD : MeasurableSet D)
    (T : ℕ) (hT : 1 ≤ T) (s : ℝ)
    (hs : (s : EReal) ≤ ⨅ ℙ' ∈ D, relEntropy ℙ' ℙ) :
    empProb ℙ T D ≤ ((T : ℝ) + 1) ^ d * Real.exp (-((T : ℝ) * s)) := by sorry

end DROOptimal.Predictor
