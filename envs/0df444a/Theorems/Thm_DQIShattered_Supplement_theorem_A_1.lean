-- Prove2me | Theorems.Thm_DQIShattered_Supplement_theorem_A_1
-- name    : DQIShattered.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:38:23.756906+00:00
-- url     : https://prove2.me/theorems/c0eb5ed2-6fac-4b73-8012-0e5f3c6cd01a
-- title:
--   Theorem A.1 — Shattering with exact classical and DQI sampling at every temperature
-- statement:
--   For every fixed integer $k\ge3$, there is a single $\alpha\in(0,1)$ and fixed positive shattering parameters such that, with high probability as $N\to\infty$, a random instance
--   $$
--   H\sim\mathbb G_{\mathrm{ER}}(N,k,\alpha k)
--   $$
--   has a solution set that shatters into exponentially many well-separated clusters and has a right-invertible incidence matrix. On the same event, the explicit classical Gaussian-elimination sampler and the ideal DQI/Regev preparation sample exactly from $\mu_{\beta,H}$ for every $\beta\in[0,\infty]$, including the uniform law on satisfying assignments at $\beta=\infty$. The classical sampler is non-stable: its expected normalized-Wasserstein change under one independently resampled clause does not tend to zero as $N\to\infty$.
--
--   Differences from the source:
--   - reading: the solution set shatters into exponentially many well-separated clusters → Lean reads “shatters” through the paper's only formal shattering notion, Definition 4.4, and quantifies fixed $\varepsilon,c>0$ for the uniform satisfying-assignment law; reason: Appendix A identifies the solution set with the zero-temperature Gibbs measure and says that this measure exhibits shattering
--   - generalization: the theorem sentence concludes that the classical and DQI algorithms sample efficiently → Lean additionally asserts that the incidence matrix has a displayed right inverse/full row rank and gives explicit cubic operation bounds; reason: the proof of Theorem A.1 establishes right-invertibility with high probability and the displayed Gaussian-elimination and trivial-code DQI procedures have the stated polynomial bounds
--   - encoding: both algorithms efficiently sample exactly at every $\beta\in[0,\infty]$ → Lean writes the explicit syndrome-and-kernel and ideal DQI/Regev output laws and requires each to equal the Gibbs law; reason: this records both named algorithms and exactness without introducing an arbitrary sampler
--   - reading: the classical algorithm is non-stable → Lean requires its expected normalized-Wasserstein change under one independently resampled clause not to tend to zero; reason: the paper explains stability asymptotically as a vanishing output-law change under clause resampling
--   - encoding: $\beta=\infty$ → Lean uses `WithTop ℝ`, with `⊤` the uniform law on solutions; reason: this represents the zero-temperature endpoint rather than dropping it or assigning a real default
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Theorem A.1 and proof, pp.35–36

import Mathlib
import Definitions.Def_DQIShattered_Supplement_Framework

namespace DQIShattered

namespace Supplement

open Filter Topology

/-- **Theorem A.1.**
Zhou, Shutty, Sellke, Jordan, arXiv:2609.40345, held version sha256 0c7f6fdf…,
pp.35–36.

For every fixed `k ≥ 3` there is a single density `α ∈ (0,1)` and fixed positive shattering
parameters such that, with probability tending to one as `N → ∞`, the solution law of a random
instance from `𝔾_ER(N,k,αk)` has exponentially many well-separated clusters and the incidence
matrix is right-invertible. On the same event, the explicit Gaussian-elimination sampler and the
ideal DQI/Regev preparation both equal the Gibbs law at every `β ∈ [0,∞]`, including the uniform
law on satisfying assignments at `β = ∞`. The explicit classical sampler is non-stable: its
expected normalized-Wasserstein change under one independently resampled clause does not vanish.

**Formalization Note** `ClusterWitness` states every clause of Definition 4.4 for the zero-
temperature law. `ExactEfficientSampling` displays the right inverse and the two concrete output
laws, rather than replacing either algorithm by an unconstrained existential distribution. -/
theorem theorem_A_1 (k : ℕ) (hk : 3 ≤ k) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ c : ℝ, 0 < c ∧
        Tendsto
            (fun N => erProb N k (α * k) fun B v =>
              ClusterWitness N (gibbsExtended B v ⊤) ε c ∧ ExactEfficientSampling B v)
            atTop (𝓝 1) ∧
          IsAsymptoticallyNonStable (k := k) (D := α * k)
            (fun _ B v => classicalRightInverseLaw B v ⊤) := by sorry

end Supplement

end DQIShattered
