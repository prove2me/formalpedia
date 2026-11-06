-- Prove2me | Theorems.Thm_BenignDegen_proposition_F_2
-- name    : BenignDegen.proposition_F_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:19.788701+00:00
-- url     : https://prove2.me/theorems/f30df868-7e90-4702-8d4a-f1c8768b89ce
-- title:
--   Proposition F.2 — $T_{\sigma,\tau}$ is $\max\{1,\tau\}/2$-averaged in $\mathsf G_\tau=\mathsf P+\tau^{-1}\mathsf P^\perp$
-- statement:
--   Let $\mathcal A:\mathbb S^p\to\mathbb R^m$ be surjective, $b\in\mathbb R^m$, $C\in\mathbb S^p$, as in the SDP pair (3.1). Fix $\sigma>0$ and $0<\tau<2$. Then $T_{\sigma,\tau}$ is $\alpha_\tau$-averaged with
--
--   $$
--   \alpha_\tau=\frac{\max\{1,\tau\}}2\quad\text{in the metric}\quad \mathsf G_\tau:=\mathsf P+\tau^{-1}\mathsf P^\perp ,
--   $$
--
--   and $\min\{1,\tau^{-1}\}\|Z\|_F^2\le\|Z\|_{\mathsf G_\tau}^2\le\max\{1,\tau^{-1}\}\|Z\|_F^2$ for every $Z$. With Lemma F.1 this turns the error bound (3.9) into linear rates for ADMM and sGS–ADMM.
--
--   Differences from the source:
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
--   - encoding: the eigenvalues of G_τ bound it between min{1, τ^{-1}} and max{1, τ^{-1}} times the Frobenius metric → min{1, τ^{-1}}‖Z‖² ≤ ⟨Z, G_τ Z⟩ ≤ max{1, τ^{-1}}‖Z‖² for all Z; reason: the same metric equivalence
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix F.3, Proposition F.2, p.29

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Proposition F.2 (a parameter-dependent metric for the shadow map), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.29.
For `0 < τ < 2`, `T_{σ,τ}` is `α_τ`-averaged with `α_τ = max{1, τ}/2` in the metric
`G_τ := P + τ^{-1}P^⊥`, and `min{1, τ^{-1}}‖Z‖_F² ≤ ‖Z‖²_{G_τ} ≤ max{1, τ^{-1}}‖Z‖_F²`. -/
theorem proposition_F_2 {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (D : SDPData ι κ) (hA : Function.Surjective D.A) (σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) (hτ2 : τ < 2) :
    IsAveragedIn (D.Gtau τ) (max 1 τ / 2) (D.T σ τ) ∧
    ∀ Z : SymMat ι, min 1 τ⁻¹ * ‖Z‖ ^ 2 ≤ gSq (D.Gtau τ) Z ∧
      gSq (D.Gtau τ) Z ≤ max 1 τ⁻¹ * ‖Z‖ ^ 2 := by sorry

end BenignDegen
