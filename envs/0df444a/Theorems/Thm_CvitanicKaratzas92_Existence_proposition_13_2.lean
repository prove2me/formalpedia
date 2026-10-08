-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Existence_proposition_13_2
-- name    : CvitanicKaratzas92.Existence.proposition_13_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:17.468362+00:00
-- url     : https://prove2.me/theorems/8ec3d109-4872-41db-8eb3-5962c71babb5
-- title:
--   Proposition 13.2 — the extended dual functional is convex, coercive, and lower semicontinuous
-- statement:
--   Under the assumptions of Theorem 13.1 and for every $y>0$, the extended dual functional $\widetilde J_y:\mathcal H\to\mathbb R\cup\{+\infty\}$ has all three properties stated in the paper:
--
--   1. $\widetilde J_y$ is convex on the finite-energy process space $\mathcal H$.
--   2. $\widetilde J_y(\nu)\to+\infty$ when the $L^2$ norm $\|\nu\|$ tends to infinity.
--   3. If $\nu_n\to\nu$ in that norm, then
--
--   $$\widetilde J_y(\nu)\leq\liminf_{n\to\infty}\widetilde J_y(\nu_n).$$
--
--   These properties supply the analytic basis for existence of a dual minimizer.
--
--   **Formalization Note** A finite-energy process is progressively measurable with finite expected integrated squared norm. Coercivity quantifies over every real threshold and a sufficiently large norm radius. The liminf is an extended-real supremum of tail infima, so $+\infty$ values are retained.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 795, Proposition 13.2 and (13.4); https://doi.org/10.1214/aoap/1177005576

import Definitions.Def_CvitanicKaratzas92_Existence_Dual

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Existence

/-- Cvitanić–Karatzas (1992), Proposition 13.2, p. 795. -/
theorem proposition_13_2 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : VProc d Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (T : ℝ≥0) (M : Market d Ω) (I : ItoOperator d Ω)
    (K : Set (Vec d)) (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (h : Standing P W 𝓕 T M I K U1 U2)
    (h58 : Cond58 T U1 U2) (h825 : CvitanicKaratzas92.Optimality.Cond825 T U1 U2)
    (h122 : Cond122 P 𝓕 T M I K U1 U2)
    (h123 : Cond123 T U1 U2) (h1211 : Cond1211 U2) :
    ∀ y : ℝ, 0 < y →
      (∀ ν₁ ν₂ : VProc d Ω,
        IsH P 𝓕 T ν₁ → IsH P 𝓕 T ν₂ →
        ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
          JyExt P 𝓕 T M I K U1 U2 y
            (fun t ω => a • ν₁ t ω + (1 - a) • ν₂ t ω) ≤
            (a : EReal) * JyExt P 𝓕 T M I K U1 U2 y ν₁ +
            ((1 - a : ℝ) : EReal) * JyExt P 𝓕 T M I K U1 U2 y ν₂) ∧
      (∀ C : ℝ, ∃ R : ℝ, 0 ≤ R ∧
        ∀ ν : VProc d Ω, IsH P 𝓕 T ν →
          R ≤ hNorm P T ν →
          (C : EReal) ≤ JyExt P 𝓕 T M I K U1 U2 y ν) ∧
      (∀ ν : VProc d Ω, IsH P 𝓕 T ν →
        ∀ νn : ℕ → VProc d Ω,
          (∀ n, IsH P 𝓕 T (νn n)) →
          Tendsto (fun n => hNorm P T
            (fun t ω => νn n t ω - ν t ω)) atTop (𝓝 0) →
          JyExt P 𝓕 T M I K U1 U2 y ν ≤
            ⨆ N : ℕ, ⨅ n : {n : ℕ // N ≤ n},
              JyExt P 𝓕 T M I K U1 U2 y (νn n.val)) := by sorry

end CvitanicKaratzas92.Existence
