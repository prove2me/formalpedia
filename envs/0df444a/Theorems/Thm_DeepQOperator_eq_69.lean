-- Prove2me | Theorems.Thm_DeepQOperator_eq_69
-- name    : DeepQOperator.eq_69
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:37.549982+00:00
-- url     : https://prove2.me/theorems/acbe8b22-4595-4434-8dec-5f676792550e
-- title:
--   (69): the anisotropic score inequality for exact affine information
-- statement:
--   Let $X\in\mathbb R^d$ have a nonnegative, continuously differentiable, compactly supported density $\rho$ with score $s=\nabla\rho/\rho$ (and $s=0$ where $\rho=0$), and assume $I=\mathbb E[s(X)s(X)^{\mathsf T}]$ is finite and positive definite. Then for every real matrix $C$ with $d$ columns and every $n\in\mathbb R^d$,
--   $$\mathbb E\,\mathrm{Var}(n^{\mathsf T}X\mid CX)\ \ge\ \sup_{v\in\ker C,\ v\ne0}\frac{(n^{\mathsf T}v)^2}{v^{\mathsf T}Iv}\ =\ \big\|\Pi_{\ker(CI^{-1/2})}I^{-1/2}n\big\|_2^2,\tag{69}$$
--   where the supremum is zero if $\ker C=\{0\}$ and $\Pi_K$ is the orthogonal projector onto $K$.
--
--   The inequality needs no regular likelihood or observation density, so it covers rank-deficient, noiseless information; it is the variance bound behind Theorem 6.
--
--   **Formalization Note** $I^{-1/2}$ is the positive definite $S$ with $S^2=I^{-1}$. The supremum is a real supremum over the nonzero kernel vectors, $0$ over an empty set.
--
--   Differences from the source:
--   - encoding: I finite → every s_j² ρ integrable; reason: equivalent for a positive semidefinite score matrix
--   - encoding: I^{−1/2} → a positive definite S with S * S = I⁻¹; reason: the positive definite square root is unique
--   - encoding: "If ker C = {0} the supremum is defined as zero" → real ⨆ over the subtype {v // Cv = 0 ∧ v ≠ 0}; reason: the real supremum of an empty family is 0
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix K.1, eq. (69), p.39 (PDF pp.42–43)

import Mathlib
import Definitions.Def_DeepQOperator_ScoreMatrix

open MeasureTheory Matrix

namespace DeepQOperator

/-- **(69), the anisotropic score inequality** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix K.1, p.39, PDF pp.42–43).

Let `X ∈ ℝ^d` have a nonnegative continuously differentiable compactly supported density `ρ`, with
score `s = ∇ρ/ρ` where `ρ > 0` and `s = 0` otherwise, and assume `I = E[s(X)s(X)ᵀ]` is finite and
positive definite. Then for every real matrix `C` with `d` columns and every `n ∈ ℝ^d`,
`E Var(nᵀX | CX) ≥ sup_{v ∈ ker C, v ≠ 0} (nᵀv)²/(vᵀIv) = ∥Π_{ker(CI^{-1/2})} I^{-1/2} n∥₂²`,
where the supremum is zero if `ker C = {0}`.

**Formalization Note.** `I^{-1/2}` is the positive definite `S` with `S * S = I⁻¹` (unique).
The supremum is a real `⨆` over the subtype `{v // Cv = 0 ∧ v ≠ 0}`, which is `0` on an empty index
type, as printed. The projection is `Submodule.starProjection` of the kernel of `C S` acting on
`EuclideanSpace ℝ (Fin d)`. `E Var(nᵀX | CX)` is `condVarExp ρ C n`. -/
theorem eq_69 {d k : ℕ} (ρ : (Fin d → ℝ) → ℝ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ContDiff ℝ 1 ρ)
    (hρK : HasCompactSupport ρ) (hρ1 : ∫ x, ρ x = 1) (hI : FiniteFisher ρ)
    (hIpd : (fisherMatrix ρ).PosDef) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (hSS : S * S = (fisherMatrix ρ)⁻¹) (C : Matrix (Fin k) (Fin d) ℝ) (n : Fin d → ℝ) :
    (⨆ v : {v : Fin d → ℝ // C *ᵥ v = 0 ∧ v ≠ 0},
        (n ⬝ᵥ v.1) ^ 2 / (v.1 ⬝ᵥ (fisherMatrix ρ *ᵥ v.1))) ≤ condVarExp ρ C n ∧
    (⨆ v : {v : Fin d → ℝ // C *ᵥ v = 0 ∧ v ≠ 0},
        (n ⬝ᵥ v.1) ^ 2 / (v.1 ⬝ᵥ (fisherMatrix ρ *ᵥ v.1))) =
      ‖(LinearMap.ker (Matrix.toEuclideanLin (C * S))).starProjection
          (WithLp.toLp 2 (S *ᵥ n))‖ ^ 2 := by sorry

end DeepQOperator
