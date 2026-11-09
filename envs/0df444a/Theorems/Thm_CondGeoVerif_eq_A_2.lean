-- Prove2me | Theorems.Thm_CondGeoVerif_eq_A_2
-- name    : CondGeoVerif.eq_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:35:28.0934+00:00
-- url     : https://prove2.me/theorems/f11c8517-d6ba-416b-bbb8-2e270a9398eb
-- title:
--   (A.2) — cross-rule lifting $R(h_{f,V})-R(h_{g,PC+NR})\le2A_{g,C,R}+2\sqrt K\|V_{g,C,R}\|_F$
-- statement:
--   Let $0<\eta<1/2$, $K\ge1$, and let $f,g:\mathbb R^K\to\{-1,1\}$ be Borel. Fix a candidate $h_{f,V}(X)=f(V^\top X)$, a revealed orthonormal frame $P\in\mathbb R^{d\times m}$, $K\le m\le d$, beginning with $V$, and a comparator $h_{g,PC+NR}(X)=g((PC+NR)^\top X)$ with $C^\top C+R^\top R=I_K$, $N\in\mathbb R^{d\times r}$ orthonormal, $P^\top N=0$, $r=\min\{K,d-m\}$. Write $U=P^\top X=(T,S)$, $Z=(I-PP^\top)X$, $E_V=\mathbf 1\{Y\ne f(T)\}$, let $\alpha(U),\gamma(U)$ be Borel dual minimizers (Lemma A.2) for $D(U,G)=\mathbf 1\{g(C^\top U+R^\top G)\ne f(T)\}$, and put $A_{g,C,R}=\mathbb E[\alpha(U)(E_V-\eta)]$, $V_{g,C,R}=\mathbb E[Z\gamma(U)^\top E_V]$. If $J_1(f,g,A;\eta)\le0$ for every contraction $A$, then every law with Gaussian feature marginal satisfies
--   $$R(h_{f,V})-R(h_{g,PC+NR})\le2A_{g,C,R}+2\sqrt K\,\|V_{g,C,R}\|_F.\qquad(A.2)$$
--   With no residual coordinates $\alpha=D$ and $V_{g,C,0}=0$. This is the certificate of the family square-root protocol.
--
--   Differences from the source:
--   - generalization: universal nonpositivity: J₁(f′, g′, A; η) ≤ 0 for every ordered pair f′, g′ ∈ F and contraction A → J₁(f, g, A; η) ≤ 0 for the pair (f, g) only, and every contraction A; reason: a weaker hypothesis; universal nonpositivity implies it
--   - generalization: duals α, γ obtained from Lemma A.2 → any Borel dual minimizers; reason: the conclusion holds for every choice
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), proof of Theorem A.5, p.22 (PDF p.25), eq. (A.2)

import Mathlib
import Definitions.Def_CondGeoVerif_liftEnvelope
import Definitions.Def_CondGeoVerif_Jprog
import Definitions.Def_CondGeoVerif_risk

set_option autoImplicit false

open MeasureTheory ProjLikeRetr.Stiefel
open scoped Matrix

namespace CondGeoVerif

/-- **Cross-rule lifting (A.2)** (Chen, *The Conditional Geometry of Statistical Verification*,
manuscript, October 2026, sha256 07a66d18…, proof of Theorem A.5, p.22 = PDF p.25). Fix a
candidate `h_{f,V}(X) = f(VᵀX)`, a revealed orthonormal frame `P ∈ ℝ^{d×m}`, `K ≤ m ≤ d`,
beginning with `V`, and a comparator `h_{g,PC+NR}(X) = g((PC + NR)ᵀX)` with `CᵀC + RᵀR = I_K`,
`N ∈ ℝ^{d×r}` orthonormal, `PᵀN = 0`, `r = min{K, d − m}`. Let `α(U)`, `γ(U)` be Borel dual
minimizers (Lemma A.2) for `D(U, G) = 1{g(CᵀU + RᵀG) ≠ f(T)}`, and
`A_{g,C,R} = E[α(U)(E_V − η)]`, `V_{g,C,R} = E[Zγ(U)ᵀE_V]`. If `J₁(f, g, A; η) ≤ 0` for every
contraction `A`, then every law with Gaussian feature marginal satisfies
`R(h_{f,V}) − R(h_{g,PC+NR}) ≤ 2A_{g,C,R} + 2√K‖V_{g,C,R}‖_F`.

**Formalization Note** The paper assumes `J₁ ≤ 0` for every ordered pair of a family and every
contraction ("universal nonpositivity"); only the pair `(f, g)` is assumed here. With no residual
coordinates (`r = 0`) the dual minimizer is `α = D` and `V_{g,C,0} = 0`, the paper's convention. -/
theorem eq_A_2 {d m K : ℕ} (hK : 1 ≤ K) (hKm : K ≤ m) (hmd : m ≤ d) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1 / 2) (f g : Vec K → Bool) (hf : Measurable f) (hg : Measurable g)
    (hJ : ∀ A : Matrix (Fin K) (Fin K) ℝ, IsContraction A → Jprog 1 f g A η ≤ 0)
    (P : Matrix (Fin d) (Fin m) ℝ) (hP : P ∈ stiefel d m) (C : Matrix (Fin m) (Fin K) ℝ)
    (R : Matrix (Fin (min K (d - m))) (Fin K) ℝ) (hCR : Cᵀ * C + Rᵀ * R = 1)
    (α : Vec m → ℝ) (γ : Vec m → Vec (min K (d - m))) (hα : Measurable α) (hγ : Measurable γ)
    (hdual : ∀ u, IsDualMin η (condDisagree f g C R u) (α u) (γ u))
    (μ : ProbabilityMeasure (Vec d × Bool)) (hμ : GaussMarginal (μ : Measure (Vec d × Bool)))
    (N : Matrix (Fin d) (Fin (min K (d - m))) ℝ) (hN : N ∈ stiefel d (min K (d - m)))
    (hPN : Pᵀ * N = 0) :
    risk (μ : Measure (Vec d × Bool)) (frameRule f (P * coordFrame m K)) -
        risk (μ : Measure (Vec d × Bool)) (frameRule g (P * C + N * R))
      ≤ 2 * scalarStat (μ : Measure (Vec d × Bool)) η f P α +
        2 * Real.sqrt K * frob (vecStat (μ : Measure (Vec d × Bool)) f P γ) := by sorry

end CondGeoVerif
