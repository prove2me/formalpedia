-- Prove2me | Theorems.Thm_BenignDegen_lemma_C_2
-- name    : BenignDegen.lemma_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:50.165615+00:00
-- url     : https://prove2.me/theorems/58852041-de89-4c23-8168-25e73ba0252a
-- title:
--   Lemma C.2 — optimal product geometry: $\mathcal Z_\star=\mathcal X_\star-\sigma\mathcal S_\star$, affine hulls and relative interiors
-- statement:
--   Let $\mathcal A:\mathbb S^p\to\mathbb R^m$ be surjective, $b\in\mathbb R^m$, $C\in\mathbb S^p$, as in the SDP pair (3.1). Suppose Assumption 3.1 holds with anchor pair $(X_{\rm sc},S_{\rm sc})$, $U=\operatorname{ran}X_{\rm sc}$, $V=\operatorname{ran}S_{\rm sc}$, and fix $\sigma>0$. Then
--
--   $$
--   \mathcal X_\star=(X_{\rm sc}+\mathcal M)\cap\mathbb S_+(U),\qquad \mathcal S_\star=(S_{\rm sc}+\mathcal L)\cap\mathbb S_+(V),\qquad \mathcal Z_\star=\operatorname{Fix}T_{\sigma,1}=\mathcal X_\star-\sigma\mathcal S_\star. \tag{C.1}
--   $$
--
--   Moreover:
--
--   1. each $\bar Z\in\mathcal Z_\star$ has a unique representation $\bar X-\sigma\bar S$ with $(\bar X,\bar S)\in\mathcal X_\star\times\mathcal S_\star$;
--   2. $\operatorname{span}(\mathcal X_\star-\mathcal X_\star)=\mathcal M$, $\operatorname{span}(\mathcal S_\star-\mathcal S_\star)=\mathcal L$, $\operatorname{aff}\mathcal Z_\star=X_{\rm sc}-\sigma S_{\rm sc}+\mathcal D$;
--   3. $\operatorname{ri}\mathcal X_\star=\{X\in\mathcal X_\star:X_{UU}\succ0\}$, $\operatorname{ri}\mathcal S_\star=\{S\in\mathcal S_\star:S_{VV}\succ0\}$ (C.2), with the relative boundaries the complementary sets;
--   4. $\bar X-\sigma\bar S\in\operatorname{ri}\mathcal Z_\star$ iff $\bar X\in\operatorname{ri}\mathcal X_\star$ and $\bar S\in\operatorname{ri}\mathcal S_\star$;
--   5. $\mathcal Z_\star$ is compact and convex.
--
--   Differences from the source:
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
--   - encoding: S(E) = {H : H = P_E H P_E}, X_UU ≻ 0, P_K M P_K ⪰ 0 → supported E (kernel of H ↦ H − P_E H P_E), PosDefOn E X (⟨v, Xv⟩ > 0 for 0 ≠ v ∈ E), PSDOn K M (⟨v, Mv⟩ ≥ 0 for v ∈ K); reason: basis-free forms of the same conditions
--   - encoding: ri, rb = cl ∖ ri → intrinsicInterior ℝ, relBdry C := C ∖ ri C; reason: rb is only applied to the closed sets X⋆, S⋆, Z⋆, where cl C ∖ ri C = C ∖ ri C
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix C.1, Lemma C.2, (C.1)–(C.2), p.17

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Lemma C.2 (optimal product geometry), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.17.
Under Assumption 3.1 with anchor pair `(X_sc, S_sc)`, `U = ran X_sc`, `V = ran S_sc`:
(C.1) `X_⋆ = (X_sc + M) ∩ S_+(U)`, `S_⋆ = (S_sc + L) ∩ S_+(V)`, `Z_⋆ = Fix T_{σ,1} = X_⋆ − σS_⋆`;
each endpoint has a unique representation `X̄ − σS̄`; `span(X_⋆ − X_⋆) = M`,
`span(S_⋆ − S_⋆) = L`, `aff Z_⋆ = X_sc − σS_sc + D`; (C.2) `ri X_⋆ = {X ∈ X_⋆ : X_UU ≻ 0}`,
`ri S_⋆ = {S ∈ S_⋆ : S_VV ≻ 0}`, with the relative boundaries the complementary sets;
`X̄ − σS̄ ∈ ri Z_⋆` iff `X̄ ∈ ri X_⋆` and `S̄ ∈ ri S_⋆`;
`Z_⋆` is compact and convex. -/
theorem lemma_C_2 {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (D : SDPData ι κ) (hA : Function.Surjective D.A) (Xsc Ssc : SymMat ι) (hAs : D.Assumption31 Xsc Ssc) (σ : ℝ) (hσ : 0 < σ) :
    D.Xstar = {X | X - Xsc ∈ D.Mdir Xsc ∧ X ∈ psdCone ι ∧ X ∈ supported (ranSub Xsc)} ∧
    D.Sstar = {S | S - Ssc ∈ D.Ldir Ssc ∧ S ∈ psdCone ι ∧ S ∈ supported (ranSub Ssc)} ∧
    D.Zstar σ = {Z | ∃ X ∈ D.Xstar, ∃ S ∈ D.Sstar, Z = X - σ • S} ∧
    (∀ X₁ ∈ D.Xstar, ∀ X₂ ∈ D.Xstar, ∀ S₁ ∈ D.Sstar, ∀ S₂ ∈ D.Sstar,
      X₁ - σ • S₁ = X₂ - σ • S₂ → X₁ = X₂ ∧ S₁ = S₂) ∧
    Submodule.span ℝ (D.Xstar - D.Xstar) = D.Mdir Xsc ∧
    Submodule.span ℝ (D.Sstar - D.Sstar) = D.Ldir Ssc ∧
    (affineSpan ℝ (D.Zstar σ) : Set (SymMat ι)) =
      {Z | Z - (Xsc - σ • Ssc) ∈ D.Ddir Xsc Ssc} ∧
    intrinsicInterior ℝ D.Xstar = {X | X ∈ D.Xstar ∧ PosDefOn (ranSub Xsc) X} ∧
    intrinsicInterior ℝ D.Sstar = {S | S ∈ D.Sstar ∧ PosDefOn (ranSub Ssc) S} ∧
    relBdry D.Xstar = {X | X ∈ D.Xstar ∧ ¬ PosDefOn (ranSub Xsc) X} ∧
    relBdry D.Sstar = {S | S ∈ D.Sstar ∧ ¬ PosDefOn (ranSub Ssc) S} ∧
    (∀ X ∈ D.Xstar, ∀ S ∈ D.Sstar, (X - σ • S ∈ intrinsicInterior ℝ (D.Zstar σ) ↔
      X ∈ intrinsicInterior ℝ D.Xstar ∧ S ∈ intrinsicInterior ℝ D.Sstar)) ∧
    IsCompact (D.Zstar σ) ∧ Convex ℝ (D.Zstar σ) := by sorry

end BenignDegen
