-- Prove2me | Theorems.Thm_ChanceStateCtrl_Robust_dual_measure_rep
-- name    : ChanceStateCtrl.Robust.dual_measure_rep
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:31.663892+00:00
-- url     : https://prove2.me/theorems/cf92d415-7fde-410a-928b-83fdc2c11ce6
-- title:
--   §3.2, p. 23 — every λ* ∈ C(D̄ × Ξ)* is integration against a (signed) regular Borel measure
-- statement:
--   Let $\bar D\subset\mathbb R^d$ and $\Xi\subset\mathbb R^m$ be compact and let $A^{-1}:L^2(D)\to C(\bar D)$ be bounded linear. Every continuous linear functional $\lambda^*$ on $C(\bar D\times\Xi)$ is integration against a finite signed Borel measure: there are finite Borel measures $\mu,\nu$ on $\bar D\times\Xi$, mutually singular, with
--   $$\langle\lambda^*,r\rangle=\int_{\bar D\times\Xi}r\,d\mu-\int_{\bar D\times\Xi}r\,d\nu\qquad\forall r\in C(\bar D\times\Xi).$$
--   In particular, for every $h\in L^2(D)$,
--   $$\langle\lambda^*,\hat{\mathcal A}^{-1}\hat{\mathcal B}h\rangle=\int_{\bar D\times\Xi}[A^{-1}h](x)\,d(\mu-\nu)(x,z).$$
--
--   This is the identification $C(\bar D\times\Xi)^*\cong\mathcal M(\bar D\times\Xi)$ that the paper uses to turn the abstract multiplier of Lemma 3.14 into a measure $\mu^*=\mu-\nu$.
--
--   **Formalization Note** The signed measure $\mu^*$ is written through its Jordan decomposition $\mu-\nu$ with $\mu\perp\nu$. On the compact metric space $\bar D\times\Xi$ every finite Borel measure is regular (Radon), so "regular Borel measure" is not a separate hypothesis. The sign convention is the paper's, $\langle r^*,r\rangle=\int r\,d\mu$.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 23, §3.2, after Lemma 3.14 (identification of C(D̄ × Ξ)* with ℳ(D̄ × Ξ), footnote 2)

import Mathlib
import Definitions.Def_ChanceStateCtrl_Robust_Setting

open MeasureTheory

namespace ChanceStateCtrl.Robust

theorem dual_measure_rep {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))}
    {Ξ : Set (EuclideanSpace ℝ (Fin m))}
    [CompactSpace (closure D)] [CompactSpace Ξ]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (lamStar : StrongDual ℝ C(closure D × Ξ, ℝ)) :
    ∃ μ ν : Measure (closure D × Ξ), IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧ μ ⟂ₘ ν ∧
      (∀ r : C(closure D × Ξ, ℝ), lamStar r = ∫ q, r q ∂μ - ∫ q, r q ∂ν) ∧
      ∀ h : ChanceStateCtrl.PDE.L2 D, lamStar (AhatBhat Ainv h) = ∫ q, Ainv h q.1 ∂μ - ∫ q, Ainv h q.1 ∂ν := by sorry

end ChanceStateCtrl.Robust
