-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Optimality_lemma_A_1
-- name    : CvitanicKaratzas92.Optimality.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:22:59.179418+00:00
-- url     : https://prove2.me/theorems/b4b5c3d4-8ed1-46fb-b46c-ace1e401d1bd
-- title:
--   Lemma A.1 — the optimal wealth $\hat X$ is strictly positive on $[0,T]$ a.s.
-- statement:
--   Assume the standing assumptions and, on the utility functions, (5.8) for $U_2$ and every $U_1(t,\cdot)$, (8.25) and (12.2). Let $x>0$ and let $(\hat\pi,\hat c)$, with wealth $\hat X$, satisfy condition (A). Then
--   $$P\big[\hat X(t)>0,\ \forall\,0\le t\le T\big]=1.$$
--
--   This is the first step of the implication (A) $\Rightarrow$ (B) of Theorem 10.1 in Appendix A.
--
--   **Formalization Note** The hypotheses (5.8), (8.25), (12.2) are those under which Appendix A works throughout (p. 805).
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 805, Appendix A, Lemma A.1

import Mathlib
import Definitions.Def_CvitanicKaratzas92_Optimality_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Optimality

/-- Cvitanić–Karatzas (1992), Lemma A.1, p. 805. Under (5.8), (8.25) and (12.2), if `(π̂, ĉ)`
with wealth `X̂` satisfies condition (A) for the capital `x > 0`, then
`P[X̂(t) > 0, ∀ 0 ≤ t ≤ T] = 1`. -/
theorem lemma_A_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) → ℝ≥0 → Ω → ℝ)
    (M : Market Ω d) (K : Set (EuclideanSpace ℝ (Fin d)))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (hS : Standing P 𝓕 T W I M K U1 U2)
    (h58_1 : ∀ t ≤ T, Cond58 (U1 t)) (h58_2 : Cond58 U2) (h825 : Cond825 T U1 U2)
    (h122 : Cond122 P 𝓕 T I M K U1 U2)
    (x : ℝ) (hx : 0 < x) (τ : Triple Ω d) (hA : CondA P 𝓕 T I M K U1 U2 x τ) :
    ∀ᵐ ω ∂P, ∀ t ≤ T, 0 < τ.X t ω := by sorry


end CvitanicKaratzas92.Optimality
