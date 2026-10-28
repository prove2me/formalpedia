-- Prove2me | Theorems.Thm_ChanceStateCtrl_Robust_lemma_3_15
-- name    : ChanceStateCtrl.Robust.lemma_3_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:55.588973+00:00
-- url     : https://prove2.me/theorems/a89683fb-75a8-415e-89c2-8a83a91da9c1
-- title:
--   Lemma 3.15, p. 24 — the measure system (66) is equivalent to (67): λ* ≥ 0 and a probability measure μ̃ on M(u*)
-- statement:
--   In the setting of (63) (Assumption 1.1, $\Xi$ compact, $A^{-1}$ the solution operator, $F$ convex and continuously Fréchet differentiable), assume $D$ and $\Xi$ are nonempty, and fix $u^*\in L^2(D)$ with $y^*=\hat{\mathcal S}(u^*)$. The following are equivalent:
--
--   1. (66): there is a nonnegative finite Borel measure $\mu^*$ on $\bar D\times\Xi$ with
--   $$\langle DF(u^*),h\rangle+\int_{\bar D\times\Xi}[A^{-1}h](x)\,d\mu^*=0\ \ \forall h,\qquad y^*\le\alpha\ \text{on }\bar D\times\Xi,\qquad \int_{\bar D\times\Xi}(y^*-\alpha)\,d\mu^*=0;$$
--   2. (67): there are $\lambda^*\in\mathbb R$ and a Borel probability measure $\tilde\mu$ on $\bar D\times\Xi$ supported on $M(u^*)$ with
--   $$\langle DF(u^*),h\rangle+\lambda^*\int_{\bar D\times\Xi}[A^{-1}h](x)\,d\tilde\mu(x,z)=0\ \ \forall h\in L^2(D),\tag{67a}$$
--   $$\lambda^*\ge0,\qquad \max_{\bar D\times\Xi}y^*\le\alpha,\qquad \lambda^*\Big(\max_{\bar D\times\Xi}y^*-\alpha\Big)=0.\tag{67b}$$
--
--   Here $M(u^*)$ is the set of maximizers of $y^*$ over $\bar D\times\Xi$. The lemma recasts the measure multiplier as a scalar multiplier times a probability measure on the active set.
--
--   **Formalization Note** "Supported on $M(u^*)$" is $\tilde\mu(M(u^*)^c)=0$; $M(u^*)$ is closed, so this is the same as $\operatorname{supp}\tilde\mu\subseteq M(u^*)$. Nonemptiness of $D$ and $\Xi$ is added: on an empty $\bar D\times\Xi$ no probability measure exists, and the paper treats $\bar D\times\Xi$ as nonempty throughout. The paper's proof divides by $\mu^*(\bar D\times\Xi)$ and does not discuss $\mu^*=0$; the statement is still true (take $\lambda^*=0$ and a Dirac measure at a maximizer), and it is posed as printed. The maximum is written as a supremum over the compact $\bar D\times\Xi$, where it is attained. Convexity and differentiability of $F$ are the standing hypotheses of §3.2.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 24, Lemma 3.15, (66), (67), M(u)

import Mathlib
import Definitions.Def_ChanceStateCtrl_Robust_Setting

open MeasureTheory

namespace ChanceStateCtrl.Robust

theorem lemma_3_15 {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} {Ξ : Set (EuclideanSpace ℝ (Fin m))}
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (hS : ChanceStateCtrl.PDE.IsClassS D) [CompactSpace (closure D)] [CompactSpace Ξ]
    (f0 : ChanceStateCtrl.PDE.L2 D) (phi : Fin m → ChanceStateCtrl.PDE.L2 D)
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (hA : ChanceStateCtrl.AlmostSure.IsSolutionOperator D Ainv) (α : ℝ)
    (F : ChanceStateCtrl.PDE.L2 D → ℝ) (hFconv : ConvexOn ℝ Set.univ F) (hFdiff : ContDiff ℝ 1 F)
    (hD0 : D.Nonempty) (hΞ0 : Ξ.Nonempty) (us : ChanceStateCtrl.PDE.L2 D) :
    (∃ μ : Measure (closure D × Ξ), IsFiniteMeasure μ ∧
        (∀ h : ChanceStateCtrl.PDE.L2 D, fderiv ℝ F us h + ∫ q, Ainv h q.1 ∂μ = 0) ∧
        (∀ q : closure D × Ξ, Shat Ainv f0 phi us q ≤ α) ∧
        ∫ q, (Shat Ainv f0 phi us q - α) ∂μ = 0) ↔
      ∃ lam : ℝ, ∃ μt : Measure (closure D × Ξ), IsProbabilityMeasure μt ∧
        μt (argmaxSet Ainv f0 phi us)ᶜ = 0 ∧
        (∀ h : ChanceStateCtrl.PDE.L2 D, fderiv ℝ F us h + lam * ∫ q, Ainv h q.1 ∂μt = 0) ∧
        0 ≤ lam ∧ (⨆ q : closure D × Ξ, Shat Ainv f0 phi us q) ≤ α ∧
        lam * ((⨆ q : closure D × Ξ, Shat Ainv f0 phi us q) - α) = 0 := by sorry

end ChanceStateCtrl.Robust
