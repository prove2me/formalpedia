-- Prove2me | Theorems.Thm_ChanceStateCtrl_AlmostSure_splitting_3_10
-- name    : ChanceStateCtrl.AlmostSure.splitting_3_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:00.863637+00:00
-- url     : https://prove2.me/theorems/e8d43c4f-5d2b-4b2b-beee-4875c01fd2d7
-- title:
--   Proof of Theorem 3.10, p. 21 — ⟨λ*, 𝒜⁻¹ℬh⟩ = 𝔼[⟨λ, A⁻¹h⟩] + ⟨λ°, 𝒜⁻¹ℬh⟩
-- statement:
--   Let $\lambda^*\in(L^\infty_{\mathbb P}(\Omega,\mathcal C(\bar D)))^*$ be decomposed as $\lambda^*=\lambda^a+\lambda^\circ$, with $\lambda^\circ$ singular and $\lambda^a$ absolutely continuous, represented by $\lambda\in\Lambda_1(\mathcal C(\bar D)^*)$:
--   $\langle\lambda^a,y\rangle=\int_\Omega\langle\lambda(\omega),y(\omega)\rangle\,d\mathbb P(\omega)$ for all $y$. Then for every $h\in L^2(D)$,
--   $$\langle\lambda^*,\mathcal A^{-1}\mathcal Bh\rangle=\mathbb E\bigl[\langle\lambda,A^{-1}h\rangle\bigr]+\langle\lambda^\circ,\mathcal A^{-1}\mathcal Bh\rangle .$$
--
--   Since $\mathcal Bh$ is the constant random element $h$, this identity rewrites (53a) as (56a).
--
--   **Formalization Note** $A^{-1}:L^2(D)\to\mathcal C(\bar D)$ is any continuous linear map here; the identity does not use the PDE.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 21, proof of Theorem 3.10, display after "recalling that ℬ is the identity"

import Mathlib
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting

open MeasureTheory

namespace ChanceStateCtrl.AlmostSure

/-- Proof of Theorem 3.10, p. 21. Let `λ* = λᵃ + λ°` with `λ°` singular and `λᵃ` absolutely
continuous, represented by `λ ∈ Λ₁(C(D̄)*)`: `⟨λᵃ, y⟩ = ∫ ⟨λ(ω), y(ω)⟩ dP(ω)`. Then for every
`h ∈ L²(D)`, `⟨λ*, 𝒜⁻¹ℬh⟩ = 𝔼[⟨λ, A⁻¹h⟩] + ⟨λ°, 𝒜⁻¹ℬh⟩`. -/
theorem splitting_3_10 {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace (closure D)]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lamStar lamA lamSing : StrongDual ℝ (Linf D P)) (lam : Ω → StrongDual ℝ C(closure D, ℝ))
    (hlam : lam ∈ Lambda1 C(closure D, ℝ) P)
    (hrep : ∀ y : Linf D P, lamA y = ∫ ω, lam ω (y ω) ∂P)
    (hsing : IsSingular P lamSing) (hsplit : lamStar = lamA + lamSing) :
    ∀ h : ChanceStateCtrl.PDE.L2 D, lamStar (Ainv.compLp (Bconst P h)) =
      ∫ ω, lam ω (Ainv h) ∂P + lamSing (Ainv.compLp (Bconst P h)) := by sorry

end ChanceStateCtrl.AlmostSure
