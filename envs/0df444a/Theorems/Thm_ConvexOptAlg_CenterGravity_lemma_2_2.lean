-- Prove2me | Theorems.Thm_ConvexOptAlg_CenterGravity_lemma_2_2
-- name    : ConvexOptAlg.CenterGravity.lemma_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:24:00.773992+00:00
-- url     : https://prove2.me/theorems/2eb4da1f-7114-43af-b616-7ae1a657c252
-- title:
--   Lemma 2.2 (Grünbaum), p. 246 — a half-space through the centroid of a convex body holds at least 1/e of its volume
-- statement:
--   This is Grünbaum's inequality (1960).
--
--   Let $\mathcal K\subset\mathbb R^n$ be a convex body (compact, convex, with non-empty interior) that is centered, i.e. $\int_{x\in\mathcal K}x\,dx=0$. Then for every $w\in\mathbb R^n$ with $w\ne0$,
--   $$\mathrm{Vol}\big(\mathcal K\cap\{x\in\mathbb R^n: x^\top w\ge0\}\big)\ \ge\ \frac1e\,\mathrm{Vol}(\mathcal K).$$
--
--   In words, every closed half-space whose boundary passes through the center of gravity of a convex body contains at least a fraction $1/e$ of its volume, whatever the dimension. It is the geometric fact that makes each cut of the center of gravity method remove a constant fraction of volume.
--
--   **Formalization Note** The book states the lemma for a "centered convex set". The hypothesis that $\mathcal K$ is a convex body (the chapter's standing object) is added so that $\int_{\mathcal K}x\,dx$ and $\mathrm{Vol}(\mathcal K)$ are genuine finite quantities; in Lean the integral of a non-integrable function is $0$, which would otherwise make every unbounded convex set "centered". $1/e$ is written $e^{-1}$, and volumes are extended non-negative reals.
-- source:
--   Bubeck, arXiv:1405.4980v2, Lemma 2.2 (Grünbaum [1960]), p. 246

import Mathlib
import Definitions.Def_ConvexOptAlg_CenterGravity_Defs

open MeasureTheory
open scoped InnerProductSpace

namespace ConvexOptAlg.CenterGravity

/-- Bubeck, arXiv:1405.4980v2, Lemma 2.2 (Grünbaum [1960]), p. 246: if the convex body `K ⊂ ℝⁿ` is
centered, `∫_{x∈K} x dx = 0`, then for every `w ≠ 0` the half-space `{x : xᵀw ≥ 0}` contains at
least a fraction `1/e` of the volume of `K`:
`Vol(K ∩ {x ∈ ℝⁿ : xᵀw ≥ 0}) ≥ (1/e) Vol(K)`.
The book says "centered convex set"; the convex-body hypothesis (compact, convex, non-empty interior, the
chapter's standing object) is added so that `∫_{x∈K} x dx` and `Vol(K)` are genuine (finite, positive). -/
theorem lemma_2_2 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K)
    (hcent : ∫ x in K, x = 0) (w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0) :
    ENNReal.ofReal (Real.exp (-1)) * volume K ≤ volume (K ∩ {x | 0 ≤ ⟪x, w⟫_ℝ}) := by sorry

end ConvexOptAlg.CenterGravity
