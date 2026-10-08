-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Optimality_eq_8_14
-- name    : CvitanicKaratzas92.Optimality.eq_8_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:12:04.889452+00:00
-- url     : https://prove2.me/theorems/6d4ed5df-2a3d-4592-b3a0-8692173740a5
-- title:
--   (8.14) (Remark 8.1) — $\mathcal A'(x)\subset\mathcal A_\nu'(x)$ and $V(x)\le V_\nu(x)$ for every $\nu\in\mathcal D$
-- statement:
--   Under the standing assumptions, let $x>0$ and $\nu\in\mathcal D$. Every pair $(\pi,c)\in\mathcal A'(x)$ also belongs to $\mathcal A_\nu'(x)$, when its wealth is computed in the auxiliary market $\mathcal M_\nu$, and
--   $$\mathcal A'(x)\subset\mathcal A_\nu'(x),\qquad V(x)\le V_\nu(x).$$
--
--   Each auxiliary market is thus at least as favourable as the constrained original one; this is the inequality behind the minimality condition (C).
--
--   **Formalization Note** Since classes are sets of triples $(\pi,c,X)$, the inclusion reads: for each $(\pi,c,X)\in\mathcal A'(x)$ there is a process $X_\nu$ with $(\pi,c,X_\nu)\in\mathcal A_\nu'(x)$.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 778, Remark 8.1, (8.14)

import Mathlib
import Definitions.Def_CvitanicKaratzas92_Optimality_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Optimality

/-- Cvitanić–Karatzas (1992), (8.14) (Remark 8.1), p. 778: for every `ν ∈ 𝒟`,
`𝒜'(x) ⊂ 𝒜_ν'(x)` — each `(π, c) ∈ 𝒜'(x)`, with its wealth `X_ν` in `𝓜_ν`, lies in
`𝒜_ν'(x)` — and `V(x) ≤ V_ν(x)`. -/
theorem eq_8_14 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) → ℝ≥0 → Ω → ℝ)
    (M : Market Ω d) (K : Set (EuclideanSpace ℝ (Fin d)))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (hS : Standing P 𝓕 T W I M K U1 U2)
    (x : ℝ) (hx : 0 < x) (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hν : IsD P 𝓕 T K ν) :
    (∀ τ ∈ A' P 𝓕 T I M K U1 U2 x, ∃ Xν : ℝ≥0 → Ω → ℝ,
      (⟨τ.π, τ.c, Xν⟩ : Triple Ω d) ∈ Anu' P 𝓕 T I M K U1 U2 ν x) ∧
    V P 𝓕 T I M K U1 U2 x ≤ Vnu P 𝓕 T I M K U1 U2 ν x := by sorry


end CvitanicKaratzas92.Optimality
