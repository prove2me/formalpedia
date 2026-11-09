-- Prove2me | Theorems.Thm_ChanTomoNB_lemma_5_5
-- name    : ChanTomoNB.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:28:34.539955+00:00
-- url     : https://prove2.me/theorems/c8d870b1-fd9e-457d-8cea-26cb48a8cfad
-- title:
--   Lemma 5.5 — $\mathbb P\{\|G\|_{\mathrm{op}}>3\sqrt{a+b}\}\le e^{-(a+b)}$ and $\mathbb P\{\sigma_{\min}(G_0)\le\sqrt m/5\}\le2e^{-m/16}$
-- statement:
--   A standard complex Gaussian has independent real and imaginary parts of variance $1/2$.
--
--   1. If $G\in\mathbb C^{a\times b}$ is a centered circular complex Gaussian matrix whose vectorized covariance $C$ satisfies $0\preceq C\preceq I$, then
--   $$
--   \mathbb P\{\|G\|_{\mathrm{op}}>3\sqrt{a+b}\}\le e^{-(a+b)} .
--   $$
--   2. If $G_0\in\mathbb C^{m\times\alpha}$ has independent $\mathcal{CN}(0,1)$ entries, $\alpha\ge1$ and $m\ge125\alpha$, then
--   $$
--   \mathbb P\{\sigma_{\min}(G_0)\le\sqrt m/5\}\le2e^{-m/16} .
--   $$
--
--   These estimates show that a Haar-random signal range is balanced with probability at least $1/2$ (Lemma 5.3).
--
--   Differences from the source:
--   - encoding: G centered circular complex Gaussian with vectorized covariance at most identity → vec G = C^{1/2} z with z ∼ CN(0, I_{ab}) and C PSD with I − C PSD; reason: the representation used in the proof (p.28); every such G has this law
--   - encoding: σ_min(G0) for G0 ∈ C^{m×α} → the square root of the least eigenvalue of G0†G0, with the hypothesis α ≥ 1; reason: σ_min is undefined for α = 0; this only excludes the undefined case
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Lemma 5.5, Eqs. (57)–(58), p.27

import Mathlib
import Definitions.Def_ChanTomoNB_matrixNorms
import Definitions.Def_ChanTomoNB_gaussianMatrix

open Matrix MeasureTheory
open scoped ComplexOrder

namespace ChanTomoNB

/-- **Lemma 5.5 (Gaussian operator-norm and least-singular-value estimates).** Chen, Oufkir,
*Quantum channel tomography: optimal bounds in the near-boundary regime*, arXiv:2611.03639v1,
Lemma 5.5, Eqs. (57)–(58), p.27: "If G ∈ C^{a×b} is centered circular complex Gaussian with
vectorized covariance at most identity, then P{‖G‖_op > 3√(a + b)} ≤ e^{−(a+b)}. If G0 ∈ C^{m×α}
has independent CN(0, 1) entries and m ≥ 125α, then P{σ_min(G0) ≤ √m/5} ≤ 2e^{−m/16}. Here a
standard complex Gaussian has independent real and imaginary parts of variance 1/2."

1. For all `a, b` and every PSD `C` on `ℂ^{ab}` with `C ⪯ I`, the matrix `G` with
   `vec G = C^{1/2} z`, `z ∼ CN(0, I_{ab})`, satisfies `P{‖G‖_op > 3√(a+b)} ≤ e^{−(a+b)}`.
2. For all `m, α` with `α ≥ 1` and `m ≥ 125 α`, the matrix `G₀ ∈ ℂ^{m×α}` with i.i.d. `CN(0, 1)`
   entries satisfies `P{σ_min(G₀) ≤ √m/5} ≤ 2 e^{−m/16}`.

**Formalization Note.** A centered circular complex Gaussian matrix with vectorized covariance
`C` is represented as `vec G = C^{1/2} z` with `z` standard (the representation used in the proof,
p.28); `C ⪯ I` is `(I − C) ⪰ 0`. Probabilities are the measure of the event under
`stdComplexGaussianVec` (independent coordinates `CN(0,1)`, real and imaginary parts of variance
`1/2`). `σ_min` is undefined for `α = 0`, so `1 ≤ α` is assumed. -/
theorem lemma_5_5 :
    (∀ (a b : ℕ) (C : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ), C.PosSemidef →
      (1 - C).PosSemidef →
      stdComplexGaussianVec (Fin a × Fin b)
          {z | 3 * Real.sqrt ((a : ℝ) + b) < opNorm (gaussCovMatrix C z)} ≤
        ENNReal.ofReal (Real.exp (-((a : ℝ) + b)))) ∧
    (∀ (m α : ℕ), 1 ≤ α → 125 * α ≤ m →
      stdComplexGaussianVec (Fin m × Fin α)
          {z | sigmaMin (toMat z) ≤ Real.sqrt m / 5} ≤
        ENNReal.ofReal (2 * Real.exp (-(m : ℝ) / 16))) := by sorry

end ChanTomoNB
