-- Prove2me | Theorems.Thm_ChanceStateCtrl_Robust_lemma_3_14_eq_66
-- name    : ChanceStateCtrl.Robust.lemma_3_14_eq_66
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:39.263605+00:00
-- url     : https://prove2.me/theorems/723ba249-1fa6-4080-a882-5accf8102ce5
-- title:
--   Lemma 3.14 and (66), pp. 23–24 — u* solves (63) iff a nonnegative measure μ* on D̄ × Ξ satisfies (66)
-- statement:
--   Let $D\subseteq\mathbb R^d$ ($d\in\{1,2,3\}$) be open, bounded and of class S, $\Xi\subset\mathbb R^m$ compact, $f_0,\varphi_i\in L^2(D)$, $A^{-1}:L^2(D)\to C(\bar D)$ the solution operator of $-\Delta y=F$, $y|_{\partial D}=0$, and $\alpha\in\mathbb R$. Consider the robust problem
--   $$\min_{u\in L^2(D)}F(u)\quad\text{s.t.}\quad -\Delta\hat y(\cdot,z)=u+f(\cdot,z),\ \ \hat y(\cdot,z)|_{\partial D}=0,\ \ \hat y(x,z)\le\alpha\ \ \forall(x,z)\in D\times\Xi,\tag{63}$$
--   with $F$ convex and continuously Fréchet differentiable, under the constraint qualification $0\in\operatorname{int}\{\hat{\mathcal G}(L^2(D))-\hat{\mathcal K}\}$. Then $u^*$ is a solution of (63) if and only if there is a nonnegative finite Borel measure $\mu^*$ on $\bar D\times\Xi$ such that, with $y^*=\hat{\mathcal S}(u^*)$,
--   $$\langle DF(u^*),h\rangle+\int_{\bar D\times\Xi}[A^{-1}h](x)\,d\mu^*(x,z)=0\quad\forall h\in L^2(D),\tag{66a}$$
--   $$y^*(x,z)\le\alpha\ \ \forall(x,z)\in\bar D\times\Xi,\qquad\int_{\bar D\times\Xi}(y^*(x,z)-\alpha)\,d\mu^*(x,z)=0,\tag{66b}$$
--   $$\mu^*\in\mathcal M(\bar D\times\Xi)\ \text{nonnegative}.\tag{66c}$$
--
--   The paper derives (66) from (65) (necessity); sufficiency is inherited from Lemma 3.14, since a nonnegative $\mu^*$ defines $\lambda^*=\int\cdot\,d\mu^*\in\hat{\mathcal K}^-$. The system is the measure-valued Karush–Kuhn–Tucker system of the robust problem, the starting point for its semi-infinite reformulations (67) and (68).
--
--   **Formalization Note** "Solution" means global minimizer. (66c) is built into the type: a Lean `Measure` is nonnegative, and `IsFiniteMeasure` makes it finite (regularity is automatic on the compact metric space $\bar D\times\Xi$). The state $y^*=\hat{\mathcal S}(u^*)$ is computed from the solution operator, which is tied to the PDE by the hypothesis that $A^{-1}F$ is the weak $H^1_0(D)\cap C(\bar D)$ solution for every $F$. $\bar D$ and $\Xi$ carry `CompactSpace` instances.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, pp. 23–24, Lemma 3.14 and (66)

import Mathlib
import Definitions.Def_ChanceStateCtrl_Robust_Setting

open MeasureTheory

namespace ChanceStateCtrl.Robust

theorem lemma_3_14_eq_66 {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} {Ξ : Set (EuclideanSpace ℝ (Fin m))}
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (hS : ChanceStateCtrl.PDE.IsClassS D) [CompactSpace (closure D)] [CompactSpace Ξ]
    (f0 : ChanceStateCtrl.PDE.L2 D) (phi : Fin m → ChanceStateCtrl.PDE.L2 D)
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (hA : ChanceStateCtrl.AlmostSure.IsSolutionOperator D Ainv) (α : ℝ)
    (F : ChanceStateCtrl.PDE.L2 D → ℝ) (hFconv : ConvexOn ℝ Set.univ F) (hFdiff : ContDiff ℝ 1 F)
    (hCQ : RobustCQ (Ξ := Ξ) Ainv f0 phi α) (us : ChanceStateCtrl.PDE.L2 D) :
    ChanceStateCtrl.General.IsSolution (robustFeasible (Ξ := Ξ) Ainv f0 phi α) F us ↔
      ∃ μ : Measure (closure D × Ξ), IsFiniteMeasure μ ∧
        (∀ h : ChanceStateCtrl.PDE.L2 D, fderiv ℝ F us h + ∫ q, Ainv h q.1 ∂μ = 0) ∧
        (∀ q : closure D × Ξ, Shat Ainv f0 phi us q ≤ α) ∧
        ∫ q, (Shat Ainv f0 phi us q - α) ∂μ = 0 := by sorry

end ChanceStateCtrl.Robust
