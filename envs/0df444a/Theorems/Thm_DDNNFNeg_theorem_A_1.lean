-- Prove2me | Theorems.Thm_DDNNFNeg_theorem_A_1
-- name    : DDNNFNeg.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:18:11.908829+00:00
-- url     : https://prove2.me/theorems/bf83bb1a-5e56-4419-a75e-ef75328f949c
-- title:
--   Theorem A.1 (Chernoff bound) — $\mathbb P[X \le (1-\delta)\mu] \le e^{-\delta^2\mu/2}$
-- statement:
--   Let $X_1, \dots, X_m$ be independent random variables taking values in $\{0, 1\}$, let $X = \sum_{i=1}^m X_i$ and $\mu = \mathbb E[X]$. Then for any $\delta \in (0,1)$,
--   $$
--   \mathbb P[X \le (1-\delta)\mu] \le e^{-\delta^2 \mu / 2}.
--   $$
--
--   This is the tail bound applied to the independent coins in the proof of Lemma 5.6.
--
--   **Formalization Note** The random variables are measurable real functions on a probability space, mutually independent, with values in $\{0,1\}$ at every point; the success probabilities are arbitrary. The paper's $n$ is written $m$.
--
--   Differences from the source:
--   - encoding: independent random variables X₁, …, X_n with values in {0,1} → measurable functions X i : Ω → ℝ on a probability space, iIndepFun, X i ω ∈ {0,1}; n renamed m; reason: Lean's representation of random variables; same instances
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Theorem A.1, p.27

import Mathlib
open MeasureTheory ProbabilityTheory

namespace DDNNFNeg

/-- **Theorem A.1** (Chernoff bound) (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.27): let `X₁, …, X_m` be independent random
variables taking values in `{0, 1}`, `X = ∑ᵢ Xᵢ` and `μ = E[X]`. Then for any `δ ∈ (0, 1)`,
`P[X ≤ (1 − δ)μ] ≤ e^{−δ²μ/2}`.

**Formalization Note** The random variables are measurable real functions on a probability
space, mutually independent (`iIndepFun`), with values in `{0, 1}` at every point; their
success probabilities are arbitrary. The paper's `n` is written `m`. -/
theorem theorem_A_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (X : Fin m → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    P.real {ω | ∑ i, X i ω ≤ (1 - δ) * ∫ ω', ∑ i, X i ω' ∂P} ≤
      Real.exp (-(δ ^ 2 * ∫ ω', ∑ i, X i ω' ∂P) / 2) := by sorry

end DDNNFNeg
