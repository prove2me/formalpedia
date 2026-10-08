-- Prove2me | Theorems.Thm_DROOptimal_Predictor_theorem_1_upper
-- name    : DROOptimal.Predictor.theorem_1_upper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:52.421867+00:00
-- url     : https://prove2.me/theorems/9e69869b-9563-48be-ba03-2c5dd695a949
-- title:
--   Theorem 1 (Weak LDP), (7a), p. 12 — limsup (1/T) log ℙ^∞(ℙ̂_T ∈ 𝒟) ≤ −inf_{ℙ′∈𝒟} I(ℙ′,ℙ)
-- statement:
--   Let $\xi_1,\xi_2,\dots$ be drawn independently from a distribution $\mathbb P$ on $\Xi=\{1,\dots,d\}$, and let $\hat{\mathbb P}_T$ be the empirical distribution of the first $T$ samples. Then for every Borel set $\mathcal D\subseteq\mathcal P$,
--   $$
--   \limsup_{T\to\infty}\frac1T\log\mathbb P^\infty\big(\hat{\mathbb P}_T\in\mathcal D\big)\le-\inf_{\mathbb P'\in\mathcal D}I(\mathbb P',\mathbb P).
--   $$
--
--   This large deviation upper bound is what makes $\hat c_r$ feasible in (5) (Theorem 3).
--
--   **Formalization Note** The statement is logarithm-free: for every real $s<\inf_{\mathbb P'\in\mathcal D}I(\mathbb P',\mathbb P)$ (an extended real), eventually $\mathbb P^\infty(\hat{\mathbb P}_T\in\mathcal D)\le e^{-sT}$. This is equivalent to the displayed bound with $\log0=-\infty$, including the case of an infinite infimum. Borel means `MeasurableSet D` in the simplex subtype.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 12, Theorem 1, (7a); proof in Appendix A, pp. 27–28

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

namespace DROOptimal.Predictor

/-- Theorem 1 (Weak LDP), (7a), p. 12: if the samples are drawn independently from ℙ ∈ 𝒫, then for
every Borel set 𝒟 ⊆ 𝒫,
limsup_{T→∞} (1/T) log ℙ^∞(ℙ̂_T ∈ 𝒟) ≤ − inf_{ℙ′ ∈ 𝒟} I(ℙ′, ℙ),
stated without logarithms: for every real s below the (`EReal`) infimum, eventually
ℙ^∞(ℙ̂_T ∈ 𝒟) ≤ e^{−sT}. -/
theorem theorem_1_upper {d : ℕ} (ℙ : Δ d) (D : Set (Δ d)) (hD : MeasurableSet D) (s : ℝ)
    (hs : (s : EReal) < ⨅ ℙ' ∈ D, relEntropy ℙ' ℙ) :
    ∀ᶠ T : ℕ in Filter.atTop, empProb ℙ T D ≤ Real.exp (-(s * (T : ℝ))) := by sorry

end DROOptimal.Predictor
