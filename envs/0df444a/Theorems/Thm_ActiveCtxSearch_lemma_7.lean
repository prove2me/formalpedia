-- Prove2me | Theorems.Thm_ActiveCtxSearch_lemma_7
-- name    : ActiveCtxSearch.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:39:57.590769+00:00
-- url     : https://prove2.me/theorems/879c1e0c-77c7-4a33-87b0-75433bc4a25e
-- title:
--   Lemma 7 (corrected: lower-bound exponent) — one-dimensional marginal of the uniform law on $B_2(d)$
-- statement:
--   Let $x\sim P_U$ be uniform on the unit ball $B_2(d)$ and let $u$ be a unit vector. For every measurable set $A\subseteq[-1,1]$,
--   $$\Pr[\langle x,u\rangle\in A]\le\sqrt{\frac{d+1}{2\pi}}\int_A e^{-(d-1)t^2/2}\,dt,$$
--   and if moreover $A\subseteq[-1/\sqrt2,1/\sqrt2]$, then
--   $$\Pr[\langle x,u\rangle\in A]\ge\sqrt{\frac{d+1}{16\pi}}\int_A e^{-(d-1)t^2}\,dt.$$
--
--   These Gaussian-type bounds on the projection of a uniform point of the ball are used to compare $P_X$-probabilities of slabs with one-dimensional integrals throughout the analysis (Lemmas 1, 3, 4, 6).
--
--   Differences from the source:
--   - correction: lower bound √((d+1)/16π) ∫_A e^{−(d−1)u²/2} du → lower bound √((d+1)/16π) ∫_A e^{−(d−1)t²} dt; reason: the printed bound is false: d = 20, A = [0.6, 1/√2] gives Pr = 0.001156 < 0.001275; the exponent of the proof's last display is used
--   - generalization: the first coordinate x₁ → ⟨x, u⟩ for any unit vector u; reason: P_U is rotation invariant; u = e₁ is the printed case, and Lemmas 1, 4 and 6 apply it to the direction w*/‖w*‖₂
--   - encoding: ℝᵈ, P_U, probabilities → EuclideanSpace ℝ (Fin d), Lebesgue measure conditioned on the closed ball, Measure.real; reason: Lean convention; same instances
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, Appendix A, Lemma 7, p.27

import Mathlib
import Definitions.Def_ActiveCtxSearch_Model

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace ActiveCtxSearch

/-- **Lemma 7** (corrected: lower-bound exponent), Chen, Liu & Wang, arXiv:2110.01072v2, p.27.
Let `x ∼ P_U` be uniform on `B₂(d)` and `u` a unit vector. For every measurable `A ⊆ [−1, 1]`,
`Pr[⟨x, u⟩ ∈ A] ≤ √((d+1)/(2π)) ∫_A e^{−(d−1)t²/2} dt`, and if `A ⊆ [−1/√2, 1/√2]` then
`Pr[⟨x, u⟩ ∈ A] ≥ √((d+1)/(16π)) ∫_A e^{−(d−1)t²} dt`.

**Formalization Note** The source states the lemma for the first coordinate `x₁`; `P_U` is
rotation invariant, and any unit direction `u` is allowed here (`u = e₁` is the printed case). The
printed lower bound has `e^{−(d−1)t²/2}`, which is false (`d = 20`, `A = [0.6, 1/√2]`); the exponent of
the proof's last display, `−(d−1)t²`, is used. -/
theorem lemma_7 (d : ℕ) (u : E d) (hu : ‖u‖ = 1) (A : Set ℝ) (hA : MeasurableSet A)
    (hA1 : A ⊆ Icc (-1) 1) :
    (PU d).real {x | ⟪x, u⟫ ∈ A} ≤
        Real.sqrt (((d : ℝ) + 1) / (2 * Real.pi)) *
          ∫ t in A, Real.exp (-((d : ℝ) - 1) * t ^ 2 / 2) ∧
      (A ⊆ Icc (-(1 / Real.sqrt 2)) (1 / Real.sqrt 2) →
        Real.sqrt (((d : ℝ) + 1) / (16 * Real.pi)) *
            ∫ t in A, Real.exp (-((d : ℝ) - 1) * t ^ 2) ≤
          (PU d).real {x | ⟪x, u⟫ ∈ A}) := by sorry

end ActiveCtxSearch
