-- Prove2me | Theorems.Thm_DROOptimal_Continuous_proposition_1_ii_general
-- name    : DROOptimal.Continuous.proposition_1_ii_general
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:35.407401+00:00
-- url     : https://prove2.me/theorems/57b95704-3c0e-4975-88a7-1dc4ebfdc02a
-- title:
--   §5, p. 24 — Proposition 1(ii) holds for the generalized relative entropy: I is jointly convex on 𝒫 × 𝒫
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ be compact and let $\mathcal P$ be the Borel probability distributions on $\Xi$. Let $I$ be the generalized relative entropy of Definition 8. For all pairs $(\mathbb P_1',\mathbb P_1),(\mathbb P_2',\mathbb P_2)\in\mathcal P\times\mathcal P$ and every $\lambda\in[0,1]$,
--   $$
--   I\big((1-\lambda)\mathbb P_1'+\lambda\mathbb P_2',\ (1-\lambda)\mathbb P_1+\lambda\mathbb P_2\big)\le(1-\lambda)\,I(\mathbb P_1',\mathbb P_1)+\lambda\,I(\mathbb P_2',\mathbb P_2).
--   $$
--
--   The paper states that the properties of Proposition 1 hold verbatim in the setting of §5. Joint convexity is used when the proof of Theorem 4 is repeated to show strong optimality of $\hat c_r$ (Theorem 10).
--
--   **Formalization Note** The mixtures are taken as measures and $I$ of the mixtures is Mathlib's `klDiv`. Values are in $[0,\infty]$ with $0\cdot\infty=0$, so the endpoints $\lambda\in\{0,1\}$ reduce to an identity.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 24 (sentence after Definition 8) with p. 12, Proposition 1(ii)

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting

namespace DROOptimal.Continuous

open MeasureTheory in
/-- Proposition 1(ii) in the setting of §5 (p. 24, with p. 12): joint convexity of the generalized
relative entropy, `I((1 − λ)ℙ′₁ + λℙ′₂, (1 − λ)ℙ₁ + λℙ₂) ≤ (1 − λ) I(ℙ′₁, ℙ₁) + λ I(ℙ′₂, ℙ₂)` for
λ ∈ [0, 1] (the variable `t` below). -/
theorem proposition_1_ii_general {d : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} (hΞ : IsCompact Ξ)
    (ℙ'₁ ℙ₁ ℙ'₂ ℙ₂ : Dist Ξ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    InformationTheory.klDiv
        (ENNReal.ofReal (1 - t) • (ℙ'₁ : Measure ↥Ξ) + ENNReal.ofReal t • (ℙ'₂ : Measure ↥Ξ))
        (ENNReal.ofReal (1 - t) • (ℙ₁ : Measure ↥Ξ) + ENNReal.ofReal t • (ℙ₂ : Measure ↥Ξ)) ≤
      ENNReal.ofReal (1 - t) * relEnt ℙ'₁ ℙ₁ + ENNReal.ofReal t * relEnt ℙ'₂ ℙ₂ := by sorry

end DROOptimal.Continuous
