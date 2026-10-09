-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_theorem_5_5
-- name    : FeinbergPOMDP.WStar.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:54.436599+00:00
-- url     : https://prove2.me/theorems/46c4a863-d0aa-4746-b744-3b546826d315
-- title:
--   Theorem 5.5 — uniform convergence of indefinite integrals under total-variation convergence gives convergence in probability
-- statement:
--   Let $\mathbb S$ be a metric space, let $h, h^{(1)}, h^{(2)}, \dots$ be Borel real functions on $\mathbb S$ bounded by a common constant, and let $\mu^{(n)} \to \mu$ in the total variation in $\mathbb P(\mathbb S)$. Suppose
--   $$\sup_{S \in \mathcal B(\mathbb S)} \Big|\int_S h^{(n)}(s)\,\mu^{(n)}(ds) - \int_S h(s)\,\mu(ds)\Big| \to 0 \qquad (n \to \infty). \tag{5.17}$$
--   Then $h^{(n)} \to h$ in $\mu$-probability, and therefore some subsequence $h^{(n_k)}$ converges to $h$ $\mu$-almost surely.
--
--   This is the step in the proof of Lemma 5.6 that turns the uniform convergence (5.25) of the integrals of the posteriors into almost sure convergence along a subsequence.
--
--   **Formalization Note.** $\mathbb S$ is a metrizable space with its Borel σ-algebra. Total-variation convergence is the function form of p. 4; (5.17) is kept in its set form, written in $\varepsilon$–$N$ form. Convergence in probability is Mathlib's `TendstoInMeasure`.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Theorem 5.5, p. 20

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace FeinbergPOMDP.WStar

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Theorem 5.5** (p. 20): let `𝕊` be a metric space, `h, h⁽ⁿ⁾` Borel, uniformly
bounded real functions on `𝕊`, `μ⁽ⁿ⁾ → μ` in the total variation, and (5.17)
`sup_{S ∈ ℬ(𝕊)} |∫_S h⁽ⁿ⁾ dμ⁽ⁿ⁾ − ∫_S h dμ| → 0`. Then `h⁽ⁿ⁾ → h` in probability `μ`, and therefore
some subsequence `h⁽ⁿᵏ⁾` converges `μ`-almost surely to `h`.

Formalization Note. `𝕊` is a metrizable space with its Borel σ-algebra. Total variation is the
function form of p. 4 (`TendstoTV`); (5.17) is kept in its set form, written without a real
supremum. "Uniformly bounded" is one `M` for `h` and all `h⁽ⁿ⁾`. Convergence in probability is
Mathlib's `TendstoInMeasure`. -/
theorem theorem_5_5 {S : Type*}
    [TopologicalSpace S] [TopologicalSpace.MetrizableSpace S] [MeasurableSpace S] [BorelSpace S]
    (h : S → ℝ) (hs : ℕ → S → ℝ) (hh : Measurable h) (hhs : ∀ n, Measurable (hs n))
    (hbd : ∃ M : ℝ, (∀ s, |h s| ≤ M) ∧ ∀ n s, |hs n s| ≤ M)
    (μ : ProbabilityMeasure S) (μs : ℕ → ProbabilityMeasure S) (hμ : TendstoTV μs μ)
    (h517 : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ B : Set S, MeasurableSet B →
      |∫ s in B, hs n s ∂(μs n : Measure S) - ∫ s in B, h s ∂(μ : Measure S)| ≤ ε) :
    TendstoInMeasure (μ : Measure S) hs atTop h ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ s ∂(μ : Measure S), Tendsto (fun k => hs (φ k) s) atTop (𝓝 (h s)) := by sorry

end FeinbergPOMDP.WStar
