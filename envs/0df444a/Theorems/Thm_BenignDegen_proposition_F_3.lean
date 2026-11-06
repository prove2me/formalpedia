-- Prove2me | Theorems.Thm_BenignDegen_proposition_F_3
-- name    : BenignDegen.proposition_F_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:38.527488+00:00
-- url     : https://prove2.me/theorems/b23b59fa-9fbf-44cc-b0b2-4d5d14b06708
-- title:
--   Proposition F.3 — the PDHG chart (F.8) maps $\mathcal W_\star$ onto $\mathcal Z_\star^{\eta_x}\times\{0\}$ and transfers the error bound
-- statement:
--   Let $\mathcal A:\mathbb S^p\to\mathbb R^m$ be surjective, $b\in\mathbb R^m$, $C\in\mathbb S^p$, as in the SDP pair (3.1). Let $\eta_x,\eta_y>0$, $T_P$ the PDHG map, $\mathcal W_\star=\operatorname{Fix}T_P$ and $\Phi(X,\lambda)=(Z,r)$ with $Z=X-\eta_x(C-\mathcal A^*\lambda)$, $r=\mathcal AX-b$ (F.8). Then $\Phi$ is an affine bijection mapping $\mathcal W_\star$ onto $\mathcal Z_\star^{\eta_x}\times\{0\}$, and
--
--   $$
--   \Phi T_P\Phi^{-1}(Z,r)-(Z,r)=L_{\eta_x,\eta_y}\bigl(r^\parallel(Z),r^\perp_{\eta_x}(Z),r\bigr) \tag{5.2}
--   $$
--
--   with the linear isomorphism $L_{\eta_x,\eta_y}:\mathcal R\times\mathcal N\times\mathbb R^m\to\mathbb S^p\times\mathbb R^m$,
--
--   $$
--   L_{\eta_x,\eta_y}(R^\parallel,R^\perp,r)=\bigl(R^\parallel-R^\perp-\mathcal A^\dagger r-\eta_x\eta_y\mathcal A^*(2\mathcal AR^\parallel-r),\ \mathcal AR^\parallel-r\bigr). \tag{F.9}
--   $$
--
--   Consequently, if the canonical residual with $\sigma=\eta_x$ satisfies (3.9), there are $c_P,t_P>0$ with $\|\delta_P(w)\|\ge c_P\operatorname{dist}(w,\mathcal W_\star)$ whenever $\operatorname{dist}(w,\mathcal W_\star)\le t_P$, where $\delta_P=T_P-\mathrm{Id}$.
--
--   Differences from the source:
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
--   - encoding: (5.2) at (Z, r); L a linear isomorphism R × N × ℝ^m → S^p × ℝ^m; Φ affine → (5.2) at (Z, r) = Φ(w) for every w; L injective on R × N × ℝ^m and onto S^p × ℝ^m (linear by its formula); Φ = linear map + Φ(0); reason: equivalent since Φ is a bijection
--   - encoding: S^p × ℝ^m with dist → WithLp 2 (SymMat ι × EuclideanSpace ℝ κ), the product Euclidean norm; reason: the standard norm on the product
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, §5, (5.2), p.10; Appendix F.4, (F.8), Proposition F.3, (F.9), pp.29–30

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Proposition F.3 (exact PDHG transfer), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.29.
Under surjectivity of `A` and `η_x, η_y > 0`, the chart `Φ(X, λ) = (X − η_x(C − A^*λ), AX − b)`
(F.8) is an affine bijection mapping `W_⋆ = Fix T_P` onto `Z_⋆^{η_x} × {0}`, and (5.2)
`ΦT_PΦ^{-1}(Z, r) − (Z, r) = L_{η_x,η_y}(r^∥(Z), r^⊥_{η_x}(Z), r)` holds with the linear
isomorphism `L_{η_x,η_y} : R × N × ℝ^m → S^p × ℝ^m` of (F.9). Consequently, if the canonical
residual with `σ = η_x` satisfies (3.9), there are `c_P, t_P > 0` with
`‖δ_P(w)‖ ≥ c_P dist(w, W_⋆)` whenever `dist(w, W_⋆) ≤ t_P`, `δ_P := T_P − Id`.

**Formalization Note** (5.2) is stated at `(Z, r) = Φ(w)` for every `w` (equivalent since `Φ` is
a bijection). That `L` is a linear isomorphism `R × N × ℝ^m → S^p × ℝ^m` is stated as injectivity
on `R × N × ℝ^m` and surjectivity onto `S^p × ℝ^m` (it is linear by its formula). -/
theorem proposition_F_3 {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (D : SDPData ι κ) (hA : Function.Surjective D.A) (ηx ηy : ℝ) (hηx : 0 < ηx) (hηy : 0 < ηy) :
    Function.Bijective (D.chart ηx) ∧
    (∃ L : PDSpace ι κ →ₗ[ℝ] PDSpace ι κ, ∀ w, D.chart ηx w = L w + D.chart ηx 0) ∧
    D.chart ηx '' D.Wstar ηx ηy = {v | pdX v ∈ D.Zstar ηx ∧ pdLam v = 0} ∧
    (∀ w : PDSpace ι κ, D.chart ηx (D.pdhgMap ηx ηy w) - D.chart ηx w =
      D.Lmap ηx ηy (D.rPar (pdX (D.chart ηx w))) (D.rPerp ηx (pdX (D.chart ηx w)))
        (pdLam (D.chart ηx w))) ∧
    (∀ a ∈ D.rowSpace, ∀ b ∈ D.nullSpace, ∀ r : EuclideanSpace ℝ κ,
      D.Lmap ηx ηy a b r = 0 → a = 0 ∧ b = 0 ∧ r = 0) ∧
    (∀ v : PDSpace ι κ, ∃ a ∈ D.rowSpace, ∃ b ∈ D.nullSpace, ∃ r : EuclideanSpace ℝ κ,
      D.Lmap ηx ηy a b r = v) ∧
    (D.ErrorBound ηx → ∃ cP > (0 : ℝ), ∃ tP > (0 : ℝ), ∀ w : PDSpace ι κ,
      Metric.infDist w (D.Wstar ηx ηy) ≤ tP →
        cP * Metric.infDist w (D.Wstar ηx ηy) ≤ ‖D.pdhgMap ηx ηy w - w‖) := by sorry

end BenignDegen
