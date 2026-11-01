-- Prove2me | Theorems.Thm_ActiveCtxSearch_lemma_8
-- name    : ActiveCtxSearch.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:39:56.202023+00:00
-- url     : https://prove2.me/theorems/f79a5cce-0f26-484d-8b8f-38b510334296
-- title:
--   Lemma 8 (corrected: lower-bound exponent) — two-dimensional marginal of the uniform law on $B_2(d)$
-- statement:
--   Let $d\ge2$, let $x\sim P_U$ be uniform on $B_2(d)$, and let $u_1,u_2$ be orthonormal. For every measurable planar set $A\subseteq[-1,1]^2$ inside the unit disk,
--   $$\Pr[(\langle x,u_1\rangle,\langle x,u_2\rangle)\in A]\le\frac{d}{2\pi}\int_A e^{-(d-2)(t_1^2+t_2^2)/2}\,dt_1\,dt_2,$$
--   and if $t_1^2+t_2^2\le 1/2$ for all $(t_1,t_2)\in A$, then
--   $$\Pr[(\langle x,u_1\rangle,\langle x,u_2\rangle)\in A]\ge\frac{d}{4\pi}\int_A e^{-(d-2)(t_1^2+t_2^2)}\,dt_1\,dt_2.$$
--
--   The lower bound is what turns a small angle between two hyperplanes into a lower bound on the excess error in Lemma 5.
--
--   Differences from the source:
--   - correction: lower bound (d/4π) ∫_A e^{−(d−2)(u₁²+u₂²)/2} → lower bound (d/4π) ∫_A e^{−(d−2)(t₁²+t₂²)}; reason: the printed bound is false: d = 20, A = {0.6 ≤ ‖t‖ ≤ 1/√2} gives Pr = 0.01055 < 0.01559
--   - generalization: the coordinates (x₁, x₂) → (⟨x, u₁⟩, ⟨x, u₂⟩) for any orthonormal u₁, u₂; reason: P_U is rotation invariant; (e₁, e₂) is the printed case
--   - encoding: A ⊆ [−1,1]² ∩ B₂(d) → A ⊆ [−1,1]² inside the planar unit disk; reason: A is a planar set, so B₂(d) there is the disk B₂(2)
--   - encoding: ℝᵈ, P_U, probabilities → EuclideanSpace ℝ (Fin d), Lebesgue measure conditioned on the closed ball, Measure.real; reason: Lean convention; same instances
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, Appendix A, Lemma 8, p.28

import Mathlib
import Definitions.Def_ActiveCtxSearch_Model

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace ActiveCtxSearch

/-- **Lemma 8** (corrected: lower-bound exponent), Chen, Liu & Wang, arXiv:2110.01072v2, p.28.
Let `d ≥ 2`, `x ∼ P_U` uniform on `B₂(d)`, and `u₁, u₂` orthonormal. For every measurable planar set
`A ⊆ [−1, 1]² ∩ B₂(2)`,
`Pr[(⟨x, u₁⟩, ⟨x, u₂⟩) ∈ A] ≤ (d/(2π)) ∫_A e^{−(d−2)(t₁² + t₂²)/2} dt₁ dt₂`, and if `t₁² + t₂² ≤ 1/2` on `A`
then `Pr[(⟨x, u₁⟩, ⟨x, u₂⟩) ∈ A] ≥ (d/(4π)) ∫_A e^{−(d−2)(t₁² + t₂²)} dt₁ dt₂`.

**Formalization Note** The source states the lemma for the coordinates `(x₁, x₂)`; any orthonormal
pair is allowed here (`(e₁, e₂)` is the printed case). The source's "`A ⊆ [−1,1]² ∩ B₂(d)`" is the
planar unit disk. The printed lower bound has `e^{−(d−2)(t₁²+t₂²)/2}`, which is false (`d = 20`,
`A = {0.6 ≤ ‖t‖ ≤ 1/√2}`); the exponent `−(d−2)(t₁² + t₂²)` is used. -/
theorem lemma_8 (d : ℕ) (hd : 2 ≤ d) (u₁ u₂ : E d) (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1)
    (h12 : ⟪u₁, u₂⟫ = 0) (A : Set (ℝ × ℝ)) (hA : MeasurableSet A)
    (hA1 : A ⊆ {t | t.1 ∈ Icc (-1) 1 ∧ t.2 ∈ Icc (-1) 1 ∧ t.1 ^ 2 + t.2 ^ 2 ≤ 1}) :
    (PU d).real {x | (⟪x, u₁⟫, ⟪x, u₂⟫) ∈ A} ≤
        (d : ℝ) / (2 * Real.pi) *
          ∫ t in A, Real.exp (-((d : ℝ) - 2) * (t.1 ^ 2 + t.2 ^ 2) / 2) ∧
      ((∀ t ∈ A, t.1 ^ 2 + t.2 ^ 2 ≤ 1 / 2) →
        (d : ℝ) / (4 * Real.pi) * ∫ t in A, Real.exp (-((d : ℝ) - 2) * (t.1 ^ 2 + t.2 ^ 2)) ≤
          (PU d).real {x | (⟪x, u₁⟫, ⟪x, u₂⟫) ∈ A}) := by sorry

end ActiveCtxSearch
