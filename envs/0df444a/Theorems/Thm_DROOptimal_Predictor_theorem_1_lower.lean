-- Prove2me | Theorems.Thm_DROOptimal_Predictor_theorem_1_lower
-- name    : DROOptimal.Predictor.theorem_1_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:55.180614+00:00
-- url     : https://prove2.me/theorems/bfb547e6-4d9f-4934-b0e3-fb65c887ac87
-- title:
--   Theorem 1 (Weak LDP), (7b), p. 12 — for ℙ > 0, liminf (1/T) log ℙ^∞(ℙ̂_T ∈ 𝒟) ≥ −inf_{ℙ′∈int 𝒟} I(ℙ′,ℙ)
-- statement:
--   Let $\xi_1,\xi_2,\dots$ be drawn independently from a distribution $\mathbb P$ on $\Xi=\{1,\dots,d\}$ with $\mathbb P(i)>0$ for every $i$, and let $\hat{\mathbb P}_T$ be the empirical distribution of the first $T$ samples. Then for every Borel set $\mathcal D\subseteq\mathcal P$,
--   $$
--   \liminf_{T\to\infty}\frac1T\log\mathbb P^\infty\big(\hat{\mathbb P}_T\in\mathcal D\big)\ge-\inf_{\mathbb P'\in\operatorname{int}\mathcal D}I(\mathbb P',\mathbb P),
--   $$
--   where the interior is taken in the subspace topology of $\mathcal P$.
--
--   This large deviation lower bound is what rules out any predictor less conservative than $\hat c_r$ (proof of Theorem 4).
--
--   **Formalization Note** The statement is logarithm-free: for every real $s>\inf_{\mathbb P'\in\operatorname{int}\mathcal D}I(\mathbb P',\mathbb P)$ (an extended real), eventually $e^{-sT}\le\mathbb P^\infty(\hat{\mathbb P}_T\in\mathcal D)$; when the infimum is $+\infty$ (e.g. empty interior) the statement is empty, as is the displayed bound. The interior is that of $\mathcal D$ in the subtype $\mathcal P$, and Borel means `MeasurableSet D` there.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 12, Theorem 1, (7b) and footnote 1; proof in Appendix A, pp. 27–28

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

namespace DROOptimal.Predictor

/-- Theorem 1 (Weak LDP), (7b), p. 12: if the samples are drawn independently from ℙ ∈ 𝒫 and ℙ > 0,
then for every Borel set 𝒟 ⊆ 𝒫,
liminf_{T→∞} (1/T) log ℙ^∞(ℙ̂_T ∈ 𝒟) ≥ − inf_{ℙ′ ∈ int 𝒟} I(ℙ′, ℙ),
with the interior taken in the relative topology of 𝒫 (footnote 1), stated without logarithms: for
every real s above the (`EReal`) infimum, eventually e^{−sT} ≤ ℙ^∞(ℙ̂_T ∈ 𝒟). -/
theorem theorem_1_lower {d : ℕ} (ℙ : Δ d) (hℙ : ∀ i, 0 < (ℙ : Fin d → ℝ) i) (D : Set (Δ d))
    (hD : MeasurableSet D) (s : ℝ)
    (hs : (⨅ ℙ' ∈ interior D, relEntropy ℙ' ℙ) < (s : EReal)) :
    ∀ᶠ T : ℕ in Filter.atTop, Real.exp (-(s * (T : ℝ))) ≤ empProb ℙ T D := by sorry

end DROOptimal.Predictor
