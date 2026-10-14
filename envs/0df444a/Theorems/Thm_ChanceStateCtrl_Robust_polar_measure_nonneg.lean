-- Prove2me | Theorems.Thm_ChanceStateCtrl_Robust_polar_measure_nonneg
-- name    : ChanceStateCtrl.Robust.polar_measure_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:40.96367+00:00
-- url     : https://prove2.me/theorems/613b6abf-86f6-4f55-b229-baa59bbf3a2f
-- title:
--   §3.2, p. 24 — λ* ∈ 𝒦̂⁻ is integration against a nonnegative measure μ*
-- statement:
--   Let $\bar D\subset\mathbb R^d$ and $\Xi\subset\mathbb R^m$ be compact. If a continuous linear functional $\lambda^*$ on $C(\bar D\times\Xi)$ lies in the polar cone
--   $$\hat{\mathcal K}^-=\{y^*\in C(\bar D\times\Xi)^*:\langle y^*,y\rangle\le0\ \ \forall y\le 0\},$$
--   then there is a nonnegative finite Borel measure $\mu^*$ on $\bar D\times\Xi$ with
--   $$\langle\lambda^*,r\rangle=\int_{\bar D\times\Xi}r(x,z)\,d\mu^*(x,z)\qquad\forall r\in C(\bar D\times\Xi).$$
--
--   This is the step that turns the multiplier of Lemma 3.14 into the nonnegative measure of (66c).
--
--   **Formalization Note** Nonnegativity is built into the type: a Lean `Measure` takes values in $[0,\infty]$, and `IsFiniteMeasure` makes it finite. Regularity is automatic on the compact metric space $\bar D\times\Xi$.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 24, §3.2, before (66) ("This implies the nonnegativity of μ∗")

import Mathlib
import Definitions.Def_ChanceStateCtrl_Robust_Setting

open MeasureTheory

namespace ChanceStateCtrl.Robust

theorem polar_measure_nonneg {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))}
    {Ξ : Set (EuclideanSpace ℝ (Fin m))}
    [CompactSpace (closure D)] [CompactSpace Ξ]
    (lamStar : StrongDual ℝ C(closure D × Ξ, ℝ)) (hlam : lamStar ∈ KhatPolar D Ξ) :
    ∃ μ : Measure (closure D × Ξ), IsFiniteMeasure μ ∧
      ∀ r : C(closure D × Ξ, ℝ), lamStar r = ∫ q, r q ∂μ := by sorry

end ChanceStateCtrl.Robust
