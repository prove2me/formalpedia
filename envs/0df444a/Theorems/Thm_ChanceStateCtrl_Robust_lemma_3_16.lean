-- Prove2me | Theorems.Thm_ChanceStateCtrl_Robust_lemma_3_16
-- name    : ChanceStateCtrl.Robust.lemma_3_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:39.61224+00:00
-- url     : https://prove2.me/theorems/baf98160-f26a-4eb4-a532-34eb83536fc6
-- title:
--   Lemma 3.16, p. 25 — (68), DF(u*) + λ* clco{[A⁻¹(·)](x) : (x, z) ∈ M(u*)} ∋ 0, iff a probability measure μ̃ gives (67a)
-- statement:
--   In the setting of (63) (Assumption 1.1, $\Xi$ compact, $A^{-1}$ the solution operator, $F$ convex and continuously Fréchet differentiable), assume $D$ and $\Xi$ are nonempty, fix $u^*\in L^2(D)$ and $\lambda^*\ge0$. For $x\in\bar D$ let $u_x\in L^2(D)$ be the representer of $h\mapsto[A^{-1}h](x)$, i.e. $\partial g_{x,z}(u^*)$. The following are equivalent:
--
--   1. the optimality condition (68), read as a single inclusion in $L^2(D)\cong L^2(D)^*$:
--   $$0\in DF(u^*)+\lambda^*\,\overline{\operatorname{co}}\{u_x : (x,z)\in M(u^*)\};\tag{68}$$
--   2. there is a Radon probability measure $\tilde\mu$ on $\bar D\times\Xi$ supported on $M(u^*)$ such that
--   $$\langle DF(u^*),h\rangle+\lambda^*\int_{\bar D\times\Xi}[A^{-1}h](x)\,d\tilde\mu(x,z)=0\quad\forall h\in L^2(D).\tag{67a}$$
--
--   The lemma links the convex-hull form of the subdifferential of the max-function $g(u)=\max_{\bar D\times\Xi}\hat{\mathcal S}(u)-\alpha$ with the measure form (67a).
--
--   **Formalization Note** The page prints (68) as "$\langle DF(u^*),h\rangle+\lambda^*\operatorname{co}\{[A^{-1}h](x)\mid(x,z)\in M(u^*)\}\ni0$ for all $h$". Read literally for each $h$ separately, the convex combination could depend on $h$, which does not give a single measure in (67a). The statement is posed as the single inclusion in $L^2(D)^*$ from which the page derives (68) ($0\in DF(u^*)+\lambda^*\partial g(u^*)$ with $\partial g(u^*)=\operatorname{clco}\{\partial g_{x,z}(u^*)\}$). The closed convex hull is kept: the page's remark that "co" suffices is not proved in infinite dimension. $DF(u^*)$ is identified with its gradient in $L^2(D)$; the norm closure of a convex set equals its weak closure.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 25, Lemma 3.16, (68), (67a)

import Mathlib
import Definitions.Def_ChanceStateCtrl_Robust_Setting

open MeasureTheory

namespace ChanceStateCtrl.Robust

theorem lemma_3_16 {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} {Ξ : Set (EuclideanSpace ℝ (Fin m))}
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (hS : ChanceStateCtrl.PDE.IsClassS D) [CompactSpace (closure D)] [CompactSpace Ξ]
    (f0 : ChanceStateCtrl.PDE.L2 D) (phi : Fin m → ChanceStateCtrl.PDE.L2 D)
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (hA : ChanceStateCtrl.AlmostSure.IsSolutionOperator D Ainv) (α : ℝ)
    (F : ChanceStateCtrl.PDE.L2 D → ℝ) (hFconv : ConvexOn ℝ Set.univ F) (hFdiff : ContDiff ℝ 1 F)
    (hD0 : D.Nonempty) (hΞ0 : Ξ.Nonempty) (us : ChanceStateCtrl.PDE.L2 D) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∃ s ∈ closure (convexHull ℝ
        (evalRep Ainv '' (Prod.fst '' argmaxSet (Ξ := Ξ) Ainv f0 phi us))),
        gradient F us + lam • s = 0) ↔
      ∃ μt : Measure (closure D × Ξ), IsProbabilityMeasure μt ∧
        μt (argmaxSet Ainv f0 phi us)ᶜ = 0 ∧
        ∀ h : ChanceStateCtrl.PDE.L2 D, fderiv ℝ F us h + lam * ∫ q, Ainv h q.1 ∂μt = 0 := by sorry

end ChanceStateCtrl.Robust
