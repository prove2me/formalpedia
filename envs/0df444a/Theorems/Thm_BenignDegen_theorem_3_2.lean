-- Prove2me | Theorems.Thm_BenignDegen_theorem_3_2
-- name    : BenignDegen.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:13.550005+00:00
-- url     : https://prove2.me/theorems/79c5b06b-a69b-4302-964d-adec87bbc1ec
-- title:
--   Theorem 3.2 — two-sided rigidity: $\mu_{\rm ri}>0$, (3.8), the error bound (3.9), $\mu_{\rm nor}>0$ and $\mathcal C=T_{\mathcal Z_\star}$ on $\mathrm{rb}\,\mathcal Z_\star$ are equivalent
-- statement:
--   Let $\mathcal A:\mathbb S^p\to\mathbb R^m$ be surjective, $b\in\mathbb R^m$, $C\in\mathbb S^p$, as in the SDP pair (3.1). Suppose Assumption 3.1 holds with anchor pair $(X_{\rm sc},S_{\rm sc})$, $U=\operatorname{ran}X_{\rm sc}$, $V=\operatorname{ran}S_{\rm sc}$, and fix $\sigma>0$. The following are equivalent:
--
--   1. (i) **Uniform interior modulus:** $\mu_{\rm ri}:=\inf\{\|\delta'_\sigma(\bar Z;H)\|_F:\bar Z\in\operatorname{ri}\mathcal Z_\star,\ H\in\mathcal D^\perp,\ \|H\|_F=1\}>0$.
--   2. (ii) **Complementarity rigidity:** for every $\bar S\in\operatorname{rb}\mathcal S_\star$ and every $\bar X\in\operatorname{rb}\mathcal X_\star$,
--   $$\{E\in\mathcal N:P_VEP_V=0,\ E\bar S=0\}=\mathcal M,\qquad \{F\in\mathcal R:P_UFP_U=0,\ \bar XF=0\}=\mathcal L. \tag{3.8}$$
--   3. (iii) **Setwise error bound:** there are $c_\sigma,t_\sigma>0$ with $\|\delta_\sigma(Z)\|_F\ge c_\sigma\operatorname{dist}_F(Z,\mathcal Z_\star)$ whenever $\operatorname{dist}_F(Z,\mathcal Z_\star)\le t_\sigma$ (3.9).
--   4. (iv) **Uniform normal modulus:** $\mu_{\rm nor}:=\inf\{\|\delta'_\sigma(\bar Z;H)\|_F:\bar Z\in\mathcal Z_\star,\ H\in N_{\mathcal Z_\star}(\bar Z),\ \|H\|_F=1\}>0$.
--   5. (v) **Exact linearization:** $\mathcal C(\bar Z)=T_{\mathcal Z_\star}(\bar Z)$ for every $\bar Z\in\operatorname{rb}\mathcal Z_\star$.
--
--   No lower bound on the nonzero eigenvalues of the varying optimal pairs is imposed. Since (ii) does not involve $\sigma$, whether the conditions hold does not depend on $\sigma$.
--
--   Differences from the source:
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
--   - encoding: directional derivative F′(z; h) := lim_{t↓0}(F(z+th) − F(z))/t → published NonsmoothNewton.Local.HasDirDerivAt (one-sided limit over t > 0); reason: the same limit
--   - encoding: T_C(z) = {h : ∃ t_k ↓ 0, z_k ∈ C, (z_k − z)/t_k → h} → published SunNLSDP.Equiv.tangentCone (contingent cone via infDist); reason: the two cones coincide for every set
--   - encoding: N_C(z), with N_C(z) = ∅ for z ∉ C → published RobinsonSR.Reduction.normalCone; reason: the same set
--   - encoding: ri, rb = cl ∖ ri → intrinsicInterior ℝ, relBdry C := C ∖ ri C; reason: rb is only applied to the closed sets X⋆, S⋆, Z⋆, where cl C ∖ ri C = C ∖ ri C
--   - encoding: μ_ri > 0, μ_nor > 0 with μ = inf of ‖δ′_σ(Z̄; H)‖_F → ∃ μ > 0 such that for every admissible (Z̄, H) the directional derivative exists and has norm ≥ μ; reason: equivalent to inf > 0 (with inf ∅ = +∞) since δ_σ is directionally differentiable; avoids the junk value sInf ∅ = 0
--   - encoding: S(E) = {H : H = P_E H P_E}, X_UU ≻ 0, P_K M P_K ⪰ 0 → supported E (kernel of H ↦ H − P_E H P_E), PosDefOn E X (⟨v, Xv⟩ > 0 for 0 ≠ v ∈ E), PSDOn K M (⟨v, Mv⟩ ≥ 0 for v ∈ K); reason: basis-free forms of the same conditions
--   - encoding: (i) ⇔ (ii) ⇔ (iii) ⇔ (iv) ⇔ (v) → List.TFAE [(i), (ii), (iii), (iv), (v)]; reason: the same equivalence
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, §3.3, (3.7)–(3.9), Theorem 3.2, p.7

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Theorem 3.2 (two-sided rigidity and exact linearization), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.7.
Under Assumption 3.1 (anchor pair `(X_sc, S_sc)`), for every `σ > 0` the following are
equivalent: (i) `μ_ri > 0`; (ii) the primal identity of (3.8) at every `S̄ ∈ rb S_⋆` and the dual
identity at every `X̄ ∈ rb X_⋆`; (iii) the setwise error bound (3.9); (iv) `μ_nor > 0`;
(v) `C(Z̄) = T_{Z_⋆}(Z̄)` for every `Z̄ ∈ rb Z_⋆`. -/
theorem theorem_3_2 {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (D : SDPData ι κ) (hA : Function.Surjective D.A) (Xsc Ssc : SymMat ι) (hAs : D.Assumption31 Xsc Ssc) (σ : ℝ)
    (hσ : 0 < σ) :
    List.TFAE [D.CondI σ Xsc Ssc, D.CondII Xsc Ssc, D.CondIII σ, D.CondIV σ, D.CondV σ] := by sorry

end BenignDegen
