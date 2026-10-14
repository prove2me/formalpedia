-- Prove2me | Theorems.Thm_ChanceStateCtrl_AlmostSure_eq_57
-- name    : ChanceStateCtrl.AlmostSure.eq_57
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:48.503886+00:00
-- url     : https://prove2.me/theorems/35597087-4030-4a36-82e7-399627b5790b
-- title:
--   (57), pp. 21–22 — λ* ∈ 𝒦⁻ splits into ⟨λ°, y⟩ ≤ 0 and 𝔼[⟨λ, y⟩] ≤ 0 for all y ∈ 𝒦
-- statement:
--   Let $\lambda^*=\lambda^a+\lambda^\circ\in(L^\infty_{\mathbb P}(\Omega,\mathcal C(\bar D)))^*$ with $\lambda^\circ$ singular relative to $\mathbb P$ and $\lambda^a$ absolutely continuous, represented by $\lambda\in\Lambda_1(\mathcal C(\bar D)^*)$. If $\lambda^*\in\mathcal K^-$, i.e. $\langle\lambda^*,y\rangle\le0$ for every $y\in\mathcal K$, then
--   $$\langle\lambda^\circ,y\rangle\le0\qquad\text{and}\qquad\langle\lambda^a,y\rangle=\mathbb E[\langle\lambda,y\rangle]\le0\qquad\forall y\in\mathcal K.\qquad(57)$$
--
--   So the sign condition on the multiplier passes separately to its singular and to its absolutely continuous part.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, pp. 21–22, proof of Theorem 3.10, (57) (with (58))

import Mathlib
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting

open MeasureTheory

namespace ChanceStateCtrl.AlmostSure

/-- (57), pp. 21–22. Let `λ* = λᵃ + λ°` with `λ°` singular and `λᵃ` absolutely continuous,
represented by `λ ∈ Λ₁(C(D̄)*)`. If `λ* ∈ 𝒦⁻`, then both `⟨λ°, y⟩ ≤ 0` and
`⟨λᵃ, y⟩ = 𝔼[⟨λ, y⟩] ≤ 0` for every `y ∈ 𝒦`. -/
theorem eq_57 {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace (closure D)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lamStar lamA lamSing : StrongDual ℝ (Linf D P)) (lam : Ω → StrongDual ℝ C(closure D, ℝ))
    (hlam : lam ∈ Lambda1 C(closure D, ℝ) P)
    (hrep : ∀ y : Linf D P, lamA y = ∫ ω, lam ω (y ω) ∂P)
    (hsing : IsSingular P lamSing) (hsplit : lamStar = lamA + lamSing)
    (hpolar : lamStar ∈ Kpolar D P) :
    ∀ y ∈ Kcone D P, lamSing y ≤ 0 ∧ ∫ ω, lam ω (y ω) ∂P ≤ 0 := by sorry

end ChanceStateCtrl.AlmostSure
