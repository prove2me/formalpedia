-- Prove2me | Theorems.Thm_FTPLLinBandit_Supplement_theorem_15
-- name    : FTPLLinBandit.Supplement.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:43:05.731774+00:00
-- url     : https://prove2.me/theorems/3d9524cf-19fc-4202-a15d-9eab760a3548
-- title:
--   Theorem 15 — optimal-design normalization with exact radii $r=1/d$ and $R=1$
-- statement:
--   Let $d\ge1$ and let $K\subset\mathbb R^d$ be compact, with $\operatorname{conv}(K)$ having nonempty interior. Among all Borel probability distributions $q$ supported on $K$, there exists an optimal design
--   $$
--   q^\star\in\operatorname*{arg\,max}_{q\in\Delta_K}\det\operatorname{Cov}(q).
--   $$
--   Its covariance $C=\operatorname{Cov}(q^\star)$ is positive definite, and with $\mu=\mathbb E_{q^\star}X$ it satisfies the leverage bound
--   $$
--   (a-\mu)^\top C^{-1}(a-\mu)\le d\qquad\text{for every }a\in K.
--   $$
--   Define
--   $$
--   W(a)=d^{-1/2}C^{-1/2}(a-\mu),\qquad A=W(K),\qquad \nu=W_\#q^\star.
--   $$
--   Then $(A,\nu)$ satisfies Assumption 1 with the exact radii $r=1/d$ and $R=1$.
--
--   Thus the optimal design simultaneously provides the exploration law, the leverage bound, and the affine normalization used by the paper's main regret theorem.
--
--   **Formalization Note** Probability laws are Mathlib Borel measures carried by $K$. Mean and covariance reuse the published generic definitions. The positive inverse square root is `(CFC.sqrt C)⁻¹`, and the transformed distribution is the push-forward `Measure.map`.
--
--   Differences from the source:
--   - encoding: $\Delta_K$ is the set of probability distributions supported on $K$ → all Borel `Measure`s with `IsProbabilityMeasure q` and $q(K^{\mathrm c})=0$; reason: this is the literal measure-theoretic meaning of $q\in\Delta_K$
--   - encoding: $\sup_{a\in K}(a-\mu)^\top C^{-1}(a-\mu)\le d$ → the equivalent pointwise inequality for every $a\in K$; reason: this avoids a real `sSup` while preserving exactly the same bound
--   - encoding: $d^{-1/2}C^{-1/2}(K-\mu)$ and its transformed law → the image and push-forward under the affine map built from `(CFC.sqrt C)⁻¹`; reason: for the positive-definite covariance this is the positive symmetric inverse square root and the same affine normalization
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Theorem 15, p.23

import Mathlib
import Definitions.Def_FTPLLinBandit_IsNormalized
import Definitions.Def_WassersteinDRO_Guarantees_covarianceMatrix

open MeasureTheory
open scoped InnerProductSpace MatrixOrder

namespace FTPLLinBandit.Supplement

/-- **Theorem 15 (optimal-design normalization).** Wei, *Follow the Perturbed Leader for Linear
Bandits: √T Regret over General Action Sets*, arXiv:2610.17818, Theorem 15, p.23.

For every compact `K ⊆ ℝ^d` whose convex hull has nonempty interior, there is a probability
law `q⋆` carried by `K` maximizing the determinant of its covariance over every such law. Its
covariance `C` is positive definite, every `a ∈ K` has leverage
`⟨a-μ, C⁻¹(a-μ)⟩ ≤ d`, and the affine image
`d⁻¹⁄² C⁻¹⁄²(K-μ)` together with the push-forward of `q⋆` satisfies Assumption 1
with the exact radii `r = 1/d` and `R = 1`.

**Formalization Note.** `q⋆` ranges over all Borel probability measures carried by `K`, not
only finitely supported designs. Mean and covariance are the published generic definitions
`WassersteinDRO.Guarantees.meanVector` and `covarianceMatrix`. The positive inverse square root
is `(CFC.sqrt C)⁻¹`; `C.PosDef` makes this the intended symmetric inverse square root. Matrix
action uses `Matrix.toEuclideanCLM`, and the transformed law is `Measure.map` under that affine
continuous map. Compact support makes all displayed Bochner integrals genuine. -/
theorem theorem_15 {d : ℕ} (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : IsCompact K) (hKfull : (interior (convexHull ℝ K)).Nonempty) :
    ∃ qstar : Measure (EuclideanSpace ℝ (Fin d)),
      IsProbabilityMeasure qstar ∧ qstar Kᶜ = 0 ∧
      (∀ q : Measure (EuclideanSpace ℝ (Fin d)),
        IsProbabilityMeasure q → q Kᶜ = 0 →
          (WassersteinDRO.Guarantees.covarianceMatrix q).det ≤
            (WassersteinDRO.Guarantees.covarianceMatrix qstar).det) ∧
      let μ := WassersteinDRO.Guarantees.meanVector qstar
      let C := WassersteinDRO.Guarantees.covarianceMatrix qstar
      C.PosDef ∧
        (∀ a ∈ K,
          inner ℝ (a - μ) (Matrix.toEuclideanCLM (𝕜 := ℝ) (C⁻¹) (a - μ)) ≤ d) ∧
        let whiten : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun a =>
          (Real.sqrt (d : ℝ))⁻¹ •
            Matrix.toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt C)⁻¹) (a - μ)
        IsNormalized (whiten '' K) (qstar.map whiten) ((d : ℝ)⁻¹) 1 := by sorry

end FTPLLinBandit.Supplement
