-- Prove2me | Theorems.Thm_CondGeoVerif_lemma_A_4
-- name    : CondGeoVerif.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:31:50.839198+00:00
-- url     : https://prove2.me/theorems/c8bfaa4e-349b-4e92-ab72-6dc62afff80c
-- title:
--   Lemma A.4 — lifting: $L_{C,R}\le J_1(A;\eta)$ and $R(h_V)-R(h_{C,R,N})\le2A_{C,R}+2\sqrt k\|V_{C,R}\|_F$
-- statement:
--   Fix a Borel rule $f:\mathbb R^k\to\{-1,1\}$, $k\ge1$, $0<\eta<1/2$, and an orthonormal basis $P\in\mathbb R^{d\times m}$, $k\le m\le d$, whose first $k$ columns are the candidate frame $V$. Put $U=P^\top X$, $T=(U_1,\dots,U_k)$, $Z=(I-PP^\top)X$, $E_V=\mathbf 1\{Y\ne f(T)\}$ and $r=\min\{k,d-m\}$. Let $C\in\mathbb R^{m\times k}$ and $R\in\mathbb R^{r\times k}$ satisfy $C^\top C+R^\top R=I_k$, let $\alpha_{C,R}(u)$ and $\gamma_{C,R}(u)\in\mathbb R^r$ be Borel dual minimizers (Lemma A.2) for $D_{C,R}(u,\cdot)$, and let $A_{C,R}$, $V_{C,R}$, $L_{C,R}$ be as in §A.4. If $A$ is the first $k$ rows of $C$, then
--   $$L_{C,R}\le J_1(A;\eta).$$
--   Thus, if $J_1(A';\eta)\le0$ for every contraction $A'$, every labeling (every law with Gaussian feature marginal) satisfies, simultaneously for every residual orientation $N$ (orthonormal $N\in\mathbb R^{d\times r}$ with $P^\top N=0$),
--   $$R(h_V)-R(h_{C,R,N})\le2A_{C,R}+2\sqrt k\,\|V_{C,R}\|_F,\qquad h_{C,R,N}(X)=f(C^\top U+R^\top N^\top Z).$$
--   This is the residual certificate of the square-root protocol.
--
--   Differences from the source:
--   - generalization: duals α_{C,R}, γ_{C,R} chosen by Lemma A.2 → any Borel dual minimizers; reason: the conclusion holds for every choice, including the paper's
--   - encoding: the r = 0 convention α_{C,0} = D_{C,0}, V_{C,0} = 0 → the same objects: for r = 0 the unique dual minimizer is α = D_{C,0}, and ℝ⁰-valued γ gives V_{C,0} = 0; reason: Lean convention; same values
--   - encoding: "every labeling" → every probability law of (X, Y) with Gaussian feature marginal; reason: the paper's laws
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Lemma A.4, p.17 (PDF p.20), with the setup of §A.4, p.16 (PDF p.19)

import Mathlib
import Definitions.Def_CondGeoVerif_liftEnvelope
import Definitions.Def_CondGeoVerif_Jprog
import Definitions.Def_CondGeoVerif_risk

set_option autoImplicit false

open MeasureTheory ProjLikeRetr.Stiefel
open scoped Matrix

namespace CondGeoVerif

/-- **Lemma A.4 (Lifting the conditional program)** (Chen, *The Conditional Geometry of
Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, p.17 = PDF p.20), with the
objects of §A.4 (p.16). Fix a Borel rule `f : ℝᵏ → {−1, 1}`, `0 < η < 1/2`, a proposed orthonormal
basis `P ∈ ℝ^{d×m}`, `k ≤ m ≤ d`, whose first `k` columns are the candidate frame `V`, and put
`U = PᵀX`, `T = (U₁, …, U_k)`, `Z = (I − PPᵀ)X`, `E_V = 1{Y ≠ f(T)}`, `r = min{k, d − m}`. Let
`C ∈ ℝ^{m×k}`, `R ∈ ℝ^{r×k}` with `CᵀC + RᵀR = I_k`, let `α_{C,R}(u)`, `γ_{C,R}(u) ∈ ℝʳ` be Borel
dual minimizers (Lemma A.2) for `D_{C,R}(u, ·)`, and let `A_{C,R}`, `V_{C,R}`, `L_{C,R}` be as in
§A.4. If `A` is the first `k` rows of `C`, then `L_{C,R} ≤ J₁(A; η)`. Thus if
`J₁(A'; η) ≤ 0` for every contraction `A'`, every labeling (every law with Gaussian feature
marginal) satisfies, simultaneously for every residual orientation `N` (orthonormal
`N ∈ ℝ^{d×r}`, `PᵀN = 0`), `R(h_V) − R(h_{C,R,N}) ≤ 2A_{C,R} + 2√k‖V_{C,R}‖_F`, where
`h_{C,R,N}(X) = f(CᵀU + RᵀNᵀZ)`.

**Formalization Note** The duals are any Borel dual minimizers, so the statement does not depend on
a choice. For `r = 0` the unique dual minimizer is `α = D_{C,0}` and `V_{C,0} = 0`, which is the
paper's convention. `d − m` is natural subtraction with `m ≤ d`. -/
theorem lemma_A_4 {d m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (hmd : m ≤ d) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1 / 2) (f : Vec k → Bool) (hf : Measurable f) (P : Matrix (Fin d) (Fin m) ℝ)
    (hP : P ∈ stiefel d m) (C : Matrix (Fin m) (Fin k) ℝ)
    (R : Matrix (Fin (min k (d - m))) (Fin k) ℝ) (hCR : Cᵀ * C + Rᵀ * R = 1)
    (α : Vec m → ℝ) (γ : Vec m → Vec (min k (d - m))) (hα : Measurable α) (hγ : Measurable γ)
    (hdual : ∀ u, IsDualMin η (condDisagree f f C R u) (α u) (γ u)) :
    liftEnvelope η f f C R ≤ Jprog 1 f f ((coordFrame m k)ᵀ * C) η ∧
    ((∀ A : Matrix (Fin k) (Fin k) ℝ, IsContraction A → Jprog 1 f f A η ≤ 0) →
      ∀ μ : ProbabilityMeasure (Vec d × Bool), GaussMarginal (μ : Measure (Vec d × Bool)) →
        ∀ N ∈ stiefel d (min k (d - m)), Pᵀ * N = 0 →
          risk (μ : Measure (Vec d × Bool)) (frameRule f (P * coordFrame m k)) -
              risk (μ : Measure (Vec d × Bool))
                (fun x => f (matVec Cᵀ (revealed P x) + matVec Rᵀ (matVec Nᵀ (resid P x))))
            ≤ 2 * scalarStat (μ : Measure (Vec d × Bool)) η f P α +
              2 * Real.sqrt k * frob (vecStat (μ : Measure (Vec d × Bool)) f P γ)) := by sorry

end CondGeoVerif
