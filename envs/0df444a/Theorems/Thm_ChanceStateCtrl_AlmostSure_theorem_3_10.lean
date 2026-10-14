-- Prove2me | Theorems.Thm_ChanceStateCtrl_AlmostSure_theorem_3_10
-- name    : ChanceStateCtrl.AlmostSure.theorem_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:01.951524+00:00
-- url     : https://prove2.me/theorems/8e11b95a-7484-47ac-b8f0-46e7c12e24f8
-- title:
--   Theorem 3.10, p. 21 — u* solves (51) iff absolutely continuous and singular multipliers satisfy (56)
-- statement:
--   Let $D\subseteq\mathbb R^d$, $d\in\{1,2,3\}$, be open, bounded and of class S, let $A^{-1}:L^2(D)\to\mathcal C(\bar D)$ be the solution operator of $-\Delta y=F$ in $D$, $y=0$ on $\partial D$, let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\tilde f\in L^\infty_{\mathbb P}(\Omega,L^2(D))$, $\alpha\in\mathbb R$, and let $F:L^2(D)\to\mathbb R$ be convex and continuously Fréchet differentiable. Consider the almost-surely state-constrained problem
--   $$\min_{u\in L^2(D)}F(u)\quad\text{s.t.}\quad -\Delta y(\cdot,\omega)=u+\tilde f(\cdot,\omega)\ \text{in }D,\ \ y(\cdot,\omega)=0\ \text{on }\partial D,\ \ y(\cdot,\omega)\le\alpha\ \text{in }D,\quad\mathbb P\text{-a.s.}\qquad(51)$$
--   and assume the constraint qualification $0\in\operatorname{int}\{\mathcal G(L^2(D))-\mathcal K\}$. Then $u^*$ is a solution of (51) if and only if there are multipliers $\lambda\in\Lambda_1(\mathcal C(\bar D)^*)$ and $\lambda^\circ\in\Lambda_\circ(\mathcal C(\bar D)^*)$ (a singular functional on $L^\infty_{\mathbb P}(\Omega,\mathcal C(\bar D))$) and a state $y^*\in L^\infty_{\mathbb P}(\Omega,\mathcal C(\bar D))$ with
--   $$DF(u^*)+\mathbb E[A^{-*}\lambda]+\mathcal B^*\mathcal A^{-*}\lambda^\circ=0,\qquad(56a)$$
--   $$Ay^*(\cdot,\omega)-u^*-\tilde f(\cdot,\omega)=0,\qquad(56b)$$
--   $$y^*(\cdot,\omega)\le\alpha,\qquad\lambda(\cdot,\omega)\ge0,\qquad\langle\lambda(\cdot,\omega),y^*(\cdot,\omega)-\boldsymbol\alpha\rangle=0,\qquad(56c)$$
--   $$\lambda^\circ\in\mathcal K^-,\qquad\langle\lambda^\circ,y^*-\boldsymbol\alpha\rangle=0,\qquad(56d)$$
--   with the pointwise conditions (in $\omega$) holding $\mathbb P$-a.s.
--
--   The theorem replaces the abstract multiplier in $(L^\infty)^*$ of Lemma 3.7 by an integrable random multiplier $\lambda$, which satisfies pointwise sign and complementarity conditions for almost every scenario, plus a singular part $\lambda^\circ$ concentrated on sets of vanishing probability.
--
--   **Formalization Note** (56a) is stated applied to every direction $h\in L^2(D)$: $\langle DF(u^*),h\rangle+\int_\Omega\langle\lambda(\omega),A^{-1}h\rangle\,d\mathbb P+\langle\lambda^\circ,\mathcal A^{-1}\mathcal Bh\rangle=0$. (56b) says that $y^*(\cdot,\omega)$ is, on $\bar D$, the weak solution in $H^1_0(D)\cap\mathcal C(\bar D)$ of $-\Delta y=u^*+\tilde f(\cdot,\omega)$, $\mathbb P$-a.s. "$y^*(\cdot,\omega)\le\alpha$ a.e. in $D$" is read as "on $\bar D$", and "$\lambda(\cdot,\omega)\ge0$ a.e. in $D$" for $\lambda(\omega)\in\mathcal C(\bar D)^*$ as positivity of the functional: $\langle\lambda(\omega),\varphi\rangle\ge0$ for all $\varphi\ge0$. "Solution" means global minimizer over the feasible set. The class-S, dimension and solution-operator hypotheses are those of Assumption 3.5.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 21, Theorem 3.10, (56)

import Mathlib
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting

open MeasureTheory

namespace ChanceStateCtrl.AlmostSure

/-- Theorem 3.10 (p. 21). Under Assumption 3.5, with `F` convex and continuously Fréchet
differentiable and the constraint qualification `0 ∈ int{𝒢(L²(D)) − 𝒦}`, `u*` is a (global)
solution of (51) iff there are `λ ∈ Λ₁(C(D̄)*)`, a singular `λ° ∈ (L∞_P(Ω, C(D̄)))*` and a state
`y* ∈ L∞_P(Ω, C(D̄))` satisfying (56a)–(56d). (56a) is stated applied to every direction `h`,
with `𝔼[A^{−*}λ] : h ↦ ∫ ⟨λ(ω), A⁻¹h⟩ dP` and `ℬ*𝒜^{−*}λ° : h ↦ ⟨λ°, 𝒜⁻¹ℬh⟩`. -/
theorem theorem_3_10 {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (hS : ChanceStateCtrl.PDE.IsClassS D) [CompactSpace (closure D)]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (hA : IsSolutionOperator D Ainv)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (α : ℝ) (F : ChanceStateCtrl.PDE.L2 D → ℝ)
    (hFconv : ConvexOn ℝ Set.univ F) (hFdiff : ContDiff ℝ 1 F)
    (hCQ : CQ P Ainv ftil α) (us : ChanceStateCtrl.PDE.L2 D) :
    ChanceStateCtrl.General.IsSolution (feasible P Ainv ftil α) F us ↔
      ∃ lam ∈ Lambda1 C(closure D, ℝ) P, ∃ lamSing : StrongDual ℝ (Linf D P),
        IsSingular P lamSing ∧ ∃ ystar : Linf D P,
          -- (56a)
          (∀ h : ChanceStateCtrl.PDE.L2 D, fderiv ℝ F us h + ∫ ω, lam ω (Ainv h) ∂P
              + lamSing (Ainv.compLp (Bconst P h)) = 0) ∧
          -- (56b)
          (∀ᵐ ω ∂P, ∃ y, ChanceStateCtrl.PDE.IsDirichletSol D (⇑(us + ftil ω)) y ∧ ∀ x : closure D, ystar ω x = y x) ∧
          -- (56c)
          (∀ᵐ ω ∂P, (∀ x : closure D, ystar ω x ≤ α) ∧
              (∀ φ : C(closure D, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ lam ω φ) ∧
              lam ω (ystar ω - ContinuousMap.const (closure D) α) = 0) ∧
          -- (56d)
          lamSing ∈ Kpolar D P ∧
          lamSing (ystar - constLinf P (ContinuousMap.const (closure D) α)) = 0 := by sorry

end ChanceStateCtrl.AlmostSure
