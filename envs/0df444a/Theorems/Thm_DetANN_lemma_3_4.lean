-- Prove2me | Theorems.Thm_DetANN_lemma_3_4
-- name    : DetANN.lemma_3_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:25:42.855738+00:00
-- url     : https://prove2.me/theorems/f8c6ff6b-d293-4f63-a4d5-e89a394c8945
-- title:
--   Lemma 3.4, p.8 — $\mathbb E\|X-\mathbb EX\|^2=\tfrac12\mathbb E\|X-X'\|^2$ and $\mathbb E\|v-X\|^2=\|v-\mathbb EX\|^2+\mathbb E\|X-\mathbb EX\|^2$
-- statement:
--   Let $X$ be a square-integrable random vector and $X'$ an independent copy of $X$. Then
--
--   $$\mathbb E\|X-\mathbb EX\|_2^2=\tfrac12\,\mathbb E\|X-X'\|_2^2,\qquad\mathbb E\|v-X\|_2^2=\|v-\mathbb EX\|_2^2+\mathbb E\|X-\mathbb EX\|_2^2\quad\text{for every vector }v.\qquad(10)$$
--
--   These are the variance identities behind the bias–variance arguments of §5 and §7.
--
--   **Formalization Note** $X$ is a function on a probability space $(\Omega,\mu)$ in $L^2$; the pair $(X,X')$ is realized on $\mu\otimes\mu$.
--
--   Differences from the source:
--   - generalization: random vectors in ℝ^d → random vectors in any complete real inner product space; reason: ℝ^d is a complete real inner product space
--   - encoding: square-integrable X and an independent copy X′ → MemLp X 2 μ on a probability space, and (X ω, X ω′) under the product measure μ ⊗ μ; reason: the product measure realizes two independent copies with the law of X
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Lemma 3.4, (10), p.8 (PDF p.8)

import Mathlib

namespace DetANN

open MeasureTheory

/-- **Lemma 3.4** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), (10), p.8).
For a square-integrable random vector `X` and an independent copy `X'`:
`E‖X − EX‖² = ½ E‖X − X'‖²` and, for every vector `v`, `E‖v − X‖² = ‖v − EX‖² + E‖X − EX‖²`.

**Formalization Note.** `X` is defined on a probability space `(Ω, μ)` with values in a complete real
inner product space `F` (the paper uses `F = ℝ^d`), and is square-integrable (`MemLp X 2 μ`), so
every integral is of an integrable function. The pair `(X, X')` of independent copies is realized as
`(X ω, X ω')` under the product measure `μ ⊗ μ`. -/
theorem lemma_3_4 {Ω F : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (X : Ω → F) (hX : MemLp X 2 μ) :
    ∫ ω, ‖X ω - ∫ ω', X ω' ∂μ‖ ^ 2 ∂μ = (1 / 2) * ∫ p, ‖X p.1 - X p.2‖ ^ 2 ∂(μ.prod μ) ∧
      ∀ v : F, ∫ ω, ‖v - X ω‖ ^ 2 ∂μ =
        ‖v - ∫ ω, X ω ∂μ‖ ^ 2 + ∫ ω, ‖X ω - ∫ ω', X ω' ∂μ‖ ^ 2 ∂μ := by sorry

end DetANN
