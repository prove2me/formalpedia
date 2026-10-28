-- Prove2me | Theorems.Thm_ChanceStateCtrl_Robust_lemma_3_14
-- name    : ChanceStateCtrl.Robust.lemma_3_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:18.988983+00:00
-- url     : https://prove2.me/theorems/a82a3b09-0c64-4b45-b0cb-7642237e7dad
-- title:
--   Lemma 3.14, p. 23 — under the CQ, u* solves (63) iff a multiplier λ* ∈ C(D̄ × Ξ)* satisfies (65)
-- statement:
--   Assume the setting of Lemma 3.13 (Assumption 1.1, $\Xi$ compact), let $A^{-1}:L^2(D)\to C(\bar D)$ be the solution operator, $\alpha\in\mathbb R$, and let $F:L^2(D)\to\mathbb R$ be convex and continuously Fréchet differentiable. Assume the constraint qualification $0\in\operatorname{int}\{\hat{\mathcal G}(L^2(D))-\hat{\mathcal K}\}$. Then $u^*$ is a (global) solution of
--   $$\min_{u\in L^2(D)}F(u)\quad\text{s.t.}\quad \hat{\mathcal G}(u)\in\hat{\mathcal K}\tag{63}$$
--   if and only if there is a multiplier $\lambda^*\in C(\bar D\times\Xi)^*$ with
--   $$\langle DF(u^*),h\rangle+\langle\lambda^*,\hat{\mathcal A}^{-1}\hat{\mathcal B}h\rangle=0\quad\forall h\in L^2(D),\tag{65a}$$
--   $$\hat{\mathcal G}(u^*)\in\hat{\mathcal K},\qquad \lambda^*\in\hat{\mathcal K}^-,\qquad \langle\lambda^*,\hat{\mathcal G}(u^*)\rangle=0.\tag{65b}$$
--   Here $[\hat{\mathcal A}^{-1}\hat{\mathcal B}h](x,z)=[A^{-1}h](x)$.
--
--   This is the abstract Karush–Kuhn–Tucker system of the robust problem; the remainder of §3.2 identifies $\lambda^*$ with a nonnegative measure.
--
--   **Formalization Note** "Solution" means global minimizer over the feasible set. Continuous Fréchet differentiability is `ContDiff ℝ 1 F`, and $DF(u^*)$ is `fderiv ℝ F us`.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 23, Lemma 3.14, (65)

import Mathlib
import Definitions.Def_ChanceStateCtrl_Robust_Setting

open MeasureTheory

namespace ChanceStateCtrl.Robust

theorem lemma_3_14 {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} {Ξ : Set (EuclideanSpace ℝ (Fin m))}
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (hS : ChanceStateCtrl.PDE.IsClassS D) [CompactSpace (closure D)] [CompactSpace Ξ]
    (f0 : ChanceStateCtrl.PDE.L2 D) (phi : Fin m → ChanceStateCtrl.PDE.L2 D)
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (hA : ChanceStateCtrl.AlmostSure.IsSolutionOperator D Ainv) (α : ℝ)
    (F : ChanceStateCtrl.PDE.L2 D → ℝ) (hFconv : ConvexOn ℝ Set.univ F) (hFdiff : ContDiff ℝ 1 F)
    (hCQ : RobustCQ (Ξ := Ξ) Ainv f0 phi α) (us : ChanceStateCtrl.PDE.L2 D) :
    ChanceStateCtrl.General.IsSolution (robustFeasible (Ξ := Ξ) Ainv f0 phi α) F us ↔
      ∃ lamStar : StrongDual ℝ C(closure D × Ξ, ℝ),
        (∀ h : ChanceStateCtrl.PDE.L2 D, fderiv ℝ F us h + lamStar (AhatBhat Ainv h) = 0) ∧
        Ghat Ainv f0 phi α us ∈ Khat D Ξ ∧ lamStar ∈ KhatPolar D Ξ ∧
        lamStar (Ghat Ainv f0 phi α us) = 0 := by sorry

end ChanceStateCtrl.Robust
