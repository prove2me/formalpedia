-- Prove2me | Theorems.Thm_BenignDegen_lemma_D_1
-- name    : BenignDegen.lemma_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:08.518311+00:00
-- url     : https://prove2.me/theorems/2ea9dc0e-4baa-4cb3-a7c0-e45e55a107c7
-- title:
--   Lemma D.1 — on $\mathrm{ri}\,\mathcal Z_\star$ the identities (3.8) are automatic and $\mathcal C(\bar Z)=\mathcal D=T_{\mathcal Z_\star}(\bar Z)$
-- statement:
--   Let $\mathcal A:\mathbb S^p\to\mathbb R^m$ be surjective, $b\in\mathbb R^m$, $C\in\mathbb S^p$, as in the SDP pair (3.1). Suppose Assumption 3.1 holds with anchor pair $(X_{\rm sc},S_{\rm sc})$, $U=\operatorname{ran}X_{\rm sc}$, $V=\operatorname{ran}S_{\rm sc}$, and fix $\sigma>0$. For $\bar S\in\operatorname{ri}\mathcal S_\star$ the primal identity in (3.8) holds, and for $\bar X\in\operatorname{ri}\mathcal X_\star$ the dual identity holds. Moreover, for every $\bar Z\in\operatorname{ri}\mathcal Z_\star$,
--
--   $$
--   \mathcal C(\bar Z)=\mathcal D=T_{\mathcal Z_\star}(\bar Z), \tag{D.2}
--   $$
--
--   without any of the conditions (i)–(v) of Theorem 3.2.
--
--   Differences from the source:
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
--   - encoding: directional derivative F′(z; h) := lim_{t↓0}(F(z+th) − F(z))/t → published NonsmoothNewton.Local.HasDirDerivAt (one-sided limit over t > 0); reason: the same limit
--   - encoding: T_C(z) = {h : ∃ t_k ↓ 0, z_k ∈ C, (z_k − z)/t_k → h} → published SunNLSDP.Equiv.tangentCone (contingent cone via infDist); reason: the two cones coincide for every set
--   - encoding: ri, rb = cl ∖ ri → intrinsicInterior ℝ, relBdry C := C ∖ ri C; reason: rb is only applied to the closed sets X⋆, S⋆, Z⋆, where cl C ∖ ri C = C ∖ ri C
--   - encoding: S(E) = {H : H = P_E H P_E}, X_UU ≻ 0, P_K M P_K ⪰ 0 → supported E (kernel of H ↦ H − P_E H P_E), PosDefOn E X (⟨v, Xv⟩ > 0 for 0 ≠ v ∈ E), PSDOn K M (⟨v, Mv⟩ ≥ 0 for v ∈ K); reason: basis-free forms of the same conditions
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix D.1, Lemma D.1, (D.2), p.20

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Lemma D.1 (automatic interior identities), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.20.
Under Assumption 3.1, for `S̄ ∈ ri S_⋆` the primal identity in (3.8) holds, and for
`X̄ ∈ ri X_⋆` the dual identity holds. Moreover, for every `Z̄ ∈ ri Z_⋆`,
`C(Z̄) = D = T_{Z_⋆}(Z̄)` (D.2), without any of the conditions (i)–(v). -/
theorem lemma_D_1 {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (D : SDPData ι κ) (hA : Function.Surjective D.A) (Xsc Ssc : SymMat ι) (hAs : D.Assumption31 Xsc Ssc) (σ : ℝ) (hσ : 0 < σ) :
    (∀ Sbar ∈ intrinsicInterior ℝ D.Sstar, D.PrimalIdentity Xsc Ssc Sbar) ∧
    (∀ Xbar ∈ intrinsicInterior ℝ D.Xstar, D.DualIdentity Xsc Ssc Xbar) ∧
    ∀ Zbar ∈ intrinsicInterior ℝ (D.Zstar σ),
      D.stallCone σ Zbar = (D.Ddir Xsc Ssc : Set (SymMat ι)) ∧
      SunNLSDP.Equiv.tangentCone (D.Zstar σ) Zbar = (D.Ddir Xsc Ssc : Set (SymMat ι)) := by sorry

end BenignDegen
