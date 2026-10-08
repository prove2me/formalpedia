-- Prove2me | Theorems.Thm_ConservativeAD_GradAE_lemma_1
-- name    : ConservativeAD.GradAE.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:00.009989+00:00
-- url     : https://prove2.me/theorems/ec97178e-4d57-4881-bade-f6f7afbd26b1
-- title:
--   Lemma 1 — $t\mapsto\max_{v\in D(\gamma(t))}\langle\dot\gamma(t),v\rangle$ is Lebesgue measurable
-- statement:
--   Let $D:\mathbb R^p\rightrightarrows\mathbb R^p$ be a set-valued map with closed graph and nonempty compact values, and let $\gamma:[0,1]\to\mathbb R^p$ be an absolutely continuous path. Then the function
--
--   $$
--   t\mapsto\max_{v\in D(\gamma(t))}\langle\dot\gamma(t),v\rangle ,
--   $$
--
--   which is defined for almost every $t\in[0,1]$, is Lebesgue measurable on $[0,1]$.
--
--   The lemma makes the circulation integrals of Definitions 1 and 2 meaningful as Lebesgue integrals. No local boundedness of $D$ is assumed.
--
--   **Formalization Note** "Lebesgue measurable, defined almost everywhere" is rendered as `AEMeasurable` with respect to Lebesgue measure restricted to $[0,1]$. Where $\gamma$ is not differentiable, `deriv γ t = 0` and the integrand equals $0$; this happens only on a null set.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 5, Lemma 1

import Mathlib
import Definitions.Def_ConservativeAD_GradAE_ConservativeField
open MeasureTheory

namespace ConservativeAD.GradAE

/-- Lemma 1: for `D` with nonempty compact values and closed graph and an absolutely
continuous path `γ`, the max-circulation `t ↦ max_{v ∈ D(γ t)} ⟨γ̇ t, v⟩` is Lebesgue measurable
on `[0, 1]` (almost-everywhere measurable for Lebesgue measure restricted to `[0, 1]`). -/
theorem lemma_1 {p : ℕ} (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p)))
    (hclosed : IsClosed {z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p) | z.2 ∈ D z.1})
    (hval : ∀ x, (D x).Nonempty ∧ IsCompact (D x))
    (γ : ℝ → EuclideanSpace ℝ (Fin p)) (hγ : AbsolutelyContinuousOnInterval γ 0 1) :
    AEMeasurable (circ D γ) (volume.restrict (Set.Icc (0:ℝ) 1)) := by sorry

end ConservativeAD.GradAE
