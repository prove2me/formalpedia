-- Prove2me | Theorems.Thm_ConservativeAD_GradAE_remark_3a
-- name    : ConservativeAD.GradAE.remark_3a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:56.107499+00:00
-- url     : https://prove2.me/theorems/8dd86e7b-b0b8-4603-b29d-bcbf5353710a
-- title:
--   Remark 3(a) — circulation integrals are path independent; every conservative field has a potential
-- statement:
--   Let $D:\mathbb R^p\rightrightarrows\mathbb R^p$ be a conservative field. Then:
--
--   1. For every $x\in\mathbb R^p$ and all absolutely continuous paths $\gamma_1,\gamma_2:[0,1]\to\mathbb R^p$ with $\gamma_1(0)=\gamma_2(0)=0$ and $\gamma_1(1)=\gamma_2(1)=x$, the max-circulation integrand along $\gamma_1$ and the min-circulation integrand along $\gamma_2$ are Lebesgue integrable on $[0,1]$, and
--   $$
--   \int_0^1\max_{v\in D(\gamma_1(t))}\langle\dot\gamma_1(t),v\rangle\,dt=\int_0^1\min_{v\in D(\gamma_2(t))}\langle\dot\gamma_2(t),v\rangle\,dt .
--   $$
--   2. Consequently there is a function $f:\mathbb R^p\to\mathbb R$ which is a potential for $D$ in the sense of Definition 2.
--
--   Path independence is what makes Definition 2 well posed: the value of the circulation integral from $0$ to $x$ depends only on $x$, and the maximum and minimum integrals coincide. Part 2 shows that the hypothesis "f is a potential for D" of Theorem 1 is satisfied by every conservative field.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 7, Remark 3(a)

import Mathlib
import Definitions.Def_ConservativeAD_GradAE_ConservativeField
open MeasureTheory

namespace ConservativeAD.GradAE

/-- Remark 3(a): for a conservative field `D`, the max-integral along any absolutely
continuous path from `0` to `x` equals the min-integral along any other such path (both
integrals exist), and consequently `D` admits a potential. -/
theorem remark_3a {p : ℕ} (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p)))
    (hD : IsConservative D) :
    (∀ (x : EuclideanSpace ℝ (Fin p)) (γ₁ γ₂ : ℝ → EuclideanSpace ℝ (Fin p)),
      AbsolutelyContinuousOnInterval γ₁ 0 1 → AbsolutelyContinuousOnInterval γ₂ 0 1 →
      γ₁ 0 = 0 → γ₂ 0 = 0 → γ₁ 1 = x → γ₂ 1 = x →
      IntervalIntegrable (circ D γ₁) volume 0 1 ∧ IntervalIntegrable (circMin D γ₂) volume 0 1 ∧
      ∫ t in (0:ℝ)..1, circ D γ₁ t = ∫ t in (0:ℝ)..1, circMin D γ₂ t) ∧
    ∃ f : EuclideanSpace ℝ (Fin p) → ℝ, IsPotential D f := by sorry

end ConservativeAD.GradAE
