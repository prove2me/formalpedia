-- Prove2me | Theorems.Thm_BenignDegen_proposition_C_4
-- name    : BenignDegen.proposition_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:51.518347+00:00
-- url     : https://prove2.me/theorems/76668e2d-8901-4f55-9a1b-eb2e7637af0d
-- title:
--   Proposition C.4 — endpoint tangent and normal cones (C.8)–(C.10)
-- statement:
--   Let $\mathcal A:\mathbb S^p\to\mathbb R^m$ be surjective, $b\in\mathbb R^m$, $C\in\mathbb S^p$, as in the SDP pair (3.1). Suppose Assumption 3.1 holds with anchor pair $(X_{\rm sc},S_{\rm sc})$, $U=\operatorname{ran}X_{\rm sc}$, $V=\operatorname{ran}S_{\rm sc}$, and fix $\sigma>0$. Let $\bar Z=\bar X-\sigma\bar S$ with $(\bar X,\bar S)\in\mathcal X_\star\times\mathcal S_\star$, $K_{\bar X}=\ker\bar X\cap U$, $K_{\bar S}=\ker\bar S\cap V$, and $\mathcal K(\bar X)=\{W\succeq0:\operatorname{ran}W\subseteq K_{\bar X}\}$, $\mathcal K(\bar S)$ likewise. Then
--
--   $$
--   \begin{aligned}
--   T_{\mathcal X_\star}(\bar X)&=\{M\in\mathcal M:P_{K_{\bar X}}MP_{K_{\bar X}}\succeq0\}, & N_{\mathcal X_\star}(\bar X)&=\mathcal M^\perp-\mathcal K(\bar X), &&(C.8)\\
--   T_{\mathcal S_\star}(\bar S)&=\{\Lambda\in\mathcal L:P_{K_{\bar S}}\Lambda P_{K_{\bar S}}\succeq0\}, & N_{\mathcal S_\star}(\bar S)&=\mathcal L^\perp-\mathcal K(\bar S), &&(C.9)\\
--   T_{\mathcal Z_\star}(\bar Z)&=T_{\mathcal X_\star}(\bar X)-\sigma T_{\mathcal S_\star}(\bar S), & N_{\mathcal Z_\star}(\bar Z)&=\mathcal D^\perp-\mathcal K(\bar X)+\mathcal K(\bar S), &&(C.10)
--   \end{aligned}
--   $$
--
--   where the sums are Minkowski sums and all cones are taken in $\mathbb S^p$.
--
--   Differences from the source:
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
--   - encoding: S(E) = {H : H = P_E H P_E}, X_UU ≻ 0, P_K M P_K ⪰ 0 → supported E (kernel of H ↦ H − P_E H P_E), PosDefOn E X (⟨v, Xv⟩ > 0 for 0 ≠ v ∈ E), PSDOn K M (⟨v, Mv⟩ ≥ 0 for v ∈ K); reason: basis-free forms of the same conditions
--   - encoding: T_C(z) = {h : ∃ t_k ↓ 0, z_k ∈ C, (z_k − z)/t_k → h} → published SunNLSDP.Equiv.tangentCone (contingent cone via infDist); reason: the two cones coincide for every set
--   - encoding: N_C(z), with N_C(z) = ∅ for z ∉ C → published RobinsonSR.Reduction.normalCone; reason: the same set
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix C.4, Proposition C.4, (C.8)–(C.10), p.19

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Proposition C.4 (endpoint cones), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.19.
Under Assumption 3.1, at `Z̄ = X̄ − σS̄ ∈ Z_⋆` with `K_X̄ = ker X̄ ∩ U`, `K_S̄ = ker S̄ ∩ V`:
(C.8) `T_{X_⋆}(X̄) = {M ∈ M : P_{K_X̄} M P_{K_X̄} ⪰ 0}`, `N_{X_⋆}(X̄) = M^⊥ − K(X̄)`;
(C.9) `T_{S_⋆}(S̄) = {Λ ∈ L : P_{K_S̄} Λ P_{K_S̄} ⪰ 0}`, `N_{S_⋆}(S̄) = L^⊥ − K(S̄)`;
(C.10) `T_{Z_⋆}(Z̄) = T_{X_⋆}(X̄) − σT_{S_⋆}(S̄)`, `N_{Z_⋆}(Z̄) = D^⊥ − K(X̄) + K(S̄)`;
sums are Minkowski sums and all cones are taken in `S^p`. -/
theorem proposition_C_4 {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (D : SDPData ι κ) (hA : Function.Surjective D.A) (Xsc Ssc : SymMat ι) (hAs : D.Assumption31 Xsc Ssc) (σ : ℝ)
    (hσ : 0 < σ) (Xbar Sbar : SymMat ι) (hX : Xbar ∈ D.Xstar) (hS : Sbar ∈ D.Sstar) :
    SunNLSDP.Equiv.tangentCone D.Xstar Xbar =
      {M | M ∈ D.Mdir Xsc ∧ PSDOn (kerSub Xbar ⊓ ranSub Xsc) M} ∧
    RobinsonSR.Reduction.normalCone D.Xstar Xbar =
      ((D.Mdir Xsc)ᗮ : Set (SymMat ι)) - kerCone (kerSub Xbar ⊓ ranSub Xsc) ∧
    SunNLSDP.Equiv.tangentCone D.Sstar Sbar =
      {Λ | Λ ∈ D.Ldir Ssc ∧ PSDOn (kerSub Sbar ⊓ ranSub Ssc) Λ} ∧
    RobinsonSR.Reduction.normalCone D.Sstar Sbar =
      ((D.Ldir Ssc)ᗮ : Set (SymMat ι)) - kerCone (kerSub Sbar ⊓ ranSub Ssc) ∧
    SunNLSDP.Equiv.tangentCone (D.Zstar σ) (Xbar - σ • Sbar) =
      SunNLSDP.Equiv.tangentCone D.Xstar Xbar - σ • SunNLSDP.Equiv.tangentCone D.Sstar Sbar ∧
    RobinsonSR.Reduction.normalCone (D.Zstar σ) (Xbar - σ • Sbar) =
      ((D.Ddir Xsc Ssc)ᗮ : Set (SymMat ι)) - kerCone (kerSub Xbar ⊓ ranSub Xsc) +
        kerCone (kerSub Sbar ⊓ ranSub Ssc) := by sorry

end BenignDegen
