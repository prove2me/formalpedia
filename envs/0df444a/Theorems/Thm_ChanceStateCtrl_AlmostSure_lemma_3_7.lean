-- Prove2me | Theorems.Thm_ChanceStateCtrl_AlmostSure_lemma_3_7
-- name    : ChanceStateCtrl.AlmostSure.lemma_3_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:52.494575+00:00
-- url     : https://prove2.me/theorems/fbd1d299-6cce-4ac1-acc1-34e1b9620cff
-- title:
--   Lemma 3.7, p. 20 — under the CQ, u* solves (51) iff a multiplier λ* ∈ (L∞_P(Ω, C(D̄)))* satisfies (53)
-- statement:
--   Let $D\subseteq\mathbb R^d$, $d\in\{1,2,3\}$, be open, bounded and of class S, let $A^{-1}:L^2(D)\to\mathcal C(\bar D)$ be the solution operator of $-\Delta y=F$, $y|_{\partial D}=0$, let $\tilde f\in L^\infty_{\mathbb P}(\Omega,L^2(D))$ and $\alpha\in\mathbb R$, and let $F:L^2(D)\to\mathbb R$ be convex and continuously Fréchet differentiable. Consider the problem (51): minimize $F(u)$ over $u\in L^2(D)$ subject to $\mathcal G(u)=\mathcal S(u)-\boldsymbol\alpha\in\mathcal K$, i.e. the random state $y(\cdot,\omega)$ of $-\Delta y=u+\tilde f(\cdot,\omega)$ satisfies $y\le\alpha$ on $\bar D$, $\mathbb P$-a.s. Assume the constraint qualification
--   $$0\in\operatorname{int}\{\mathcal G(L^2(D))-\mathcal K\}.$$
--   Then $u^*$ is a solution of (51) if and only if there is a multiplier $\lambda^*\in(L^\infty_{\mathbb P}(\Omega,\mathcal C(\bar D)))^*$ with
--   $$\langle DF(u^*),h\rangle+\langle\lambda^*,\mathcal A^{-1}\mathcal Bh\rangle=0\quad\forall h\in L^2(D),\qquad(53a)$$
--   $$\mathcal G(u^*)\in\mathcal K,\qquad\lambda^*\in\mathcal K^-,\qquad\langle\lambda^*,\mathcal G(u^*)\rangle=0.\qquad(53b)$$
--
--   This is the abstract Karush–Kuhn–Tucker system whose multiplier lives in the dual of $L^\infty$; Theorem 3.10 refines it.
--
--   **Formalization Note** "Solution" means global minimizer over the feasible set. $DF(u^*)$ is `fderiv ℝ F us` and continuous Fréchet differentiability is `ContDiff ℝ 1 F`. $\mathcal A^{-1}\mathcal Bh$ is the constant random element $h$ pushed through $A^{-1}$ (`Ainv.compLp (Bconst P h)`).
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 20, Lemma 3.7, (53)

import Mathlib
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting

open MeasureTheory

namespace ChanceStateCtrl.AlmostSure

/-- Lemma 3.7 (p. 20). Under Assumption 3.5, with `F` convex and continuously Fréchet
differentiable on `L²(D)` and the constraint qualification `0 ∈ int{𝒢(L²(D)) − 𝒦}`, `u*` is a
(global) solution of (51) iff some `λ* ∈ (L∞_P(Ω, C(D̄)))*` satisfies
(53a) `⟨DF(u*), h⟩ + ⟨λ*, 𝒜⁻¹ℬh⟩ = 0` for all `h ∈ L²(D)` and
(53b) `𝒢(u*) ∈ 𝒦`, `λ* ∈ 𝒦⁻`, `⟨λ*, 𝒢(u*)⟩ = 0`. -/
theorem lemma_3_7 {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (hS : ChanceStateCtrl.PDE.IsClassS D) [CompactSpace (closure D)]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (hA : IsSolutionOperator D Ainv)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (α : ℝ) (F : ChanceStateCtrl.PDE.L2 D → ℝ)
    (hFconv : ConvexOn ℝ Set.univ F) (hFdiff : ContDiff ℝ 1 F)
    (hCQ : CQ P Ainv ftil α) (us : ChanceStateCtrl.PDE.L2 D) :
    ChanceStateCtrl.General.IsSolution (feasible P Ainv ftil α) F us ↔
      ∃ lamStar : StrongDual ℝ (Linf D P),
        (∀ h : ChanceStateCtrl.PDE.L2 D, fderiv ℝ F us h + lamStar (Ainv.compLp (Bconst P h)) = 0) ∧
        Gop P Ainv ftil α us ∈ Kcone D P ∧ lamStar ∈ Kpolar D P ∧
        lamStar (Gop P Ainv ftil α us) = 0 := by sorry

end ChanceStateCtrl.AlmostSure
