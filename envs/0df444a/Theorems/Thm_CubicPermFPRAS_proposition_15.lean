-- Prove2me | Theorems.Thm_CubicPermFPRAS_proposition_15
-- name    : CubicPermFPRAS.proposition_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:41.655195+00:00
-- url     : https://prove2.me/theorems/da6db8ff-4cae-4ec4-88ea-86a3e43ddd4e
-- title:
--   Proposition 15, p.14 — exact simulation of the assignment Glauber dynamics in time $O(n+Q_T\log n)$
-- statement:
--   Let $B$ have positive entries and rows summing to $1$, $J\ge0$, $a>0$, $T\ge0$ and $\sigma$ an initial assignment. The stage simulation with resampling limit $R$ simulates the dynamics exactly up to time $T$:
--
--   1. for every $\tau$, the probability that the simulation observes at most $R$ resampling events and outputs $\tau$ tends, as $R\to\infty$, to $(e^{-TL_a})(\sigma,\tau)$;
--   2. on every tape its cost is $n+5+\min(Q_T,R)\,(\lceil\log_2(2n)\rceil+7)$, where $Q_T$ is the number of resampling events up to time $T$: initialization $O(n)$, and $O(\log n)$ per resampling.
--
--   Differences from the source:
--   - generalization: the rescaled matrix $B$ of Eq. (10) and $J=J_\alpha n^2$ → every matrix $B$ with positive entries and rows summing to $1$, and every $J\ge0$; reason: the rescaled matrix is such a matrix; the proofs (§8.2–8.3) use only these properties
--   - encoding: "simulated exactly up to time $T$"; "in time $O(n+Q_T\log n)$" → the law of the $R$-limited simulation on $\{Q_T\le R\}$ converges to row $\sigma$ of $e^{-TL_a}$ as $R\to\infty$; the charged cost equals $n+5+\min(Q_T,R)(\lceil\log_2 2n\rceil+7)$; reason: the unlimited simulation reads an unbounded number of uniforms; on $\{Q_T\le R\}$ the two simulations agree and $Q_T$ is almost surely finite, so the limit is exactness; the cost identity is the paper's per-step accounting with explicit charges
--   - encoding: an $n\times n$ instance ($V_1$, $V_2$ of size $n$) → the hypothesis $1\le n$; reason: the paper's vertex classes $V_1,V_2$ are nonempty throughout (an anchor $r\in V_1$ exists); $n=0$ is no instance of the source
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Proposition 15, p.14 (PDF 16); proof, p.50 (PDF 52)

import Mathlib
import Definitions.Def_CubicPermFPRAS_sampler

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Proposition 15** (exact simulation), p.14 (PDF 16), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…); proved on p.50 (PDF 52).

After a shared `O(n²)`-time preprocessing step for `B`, the assignment Glauber dynamics can be
simulated exactly up to any fixed time `T ≥ 0`, from any initial configuration, in time
`O(n + Q_T log n)`; the initialization takes `O(n)` time and each resampling `O(log n)` time.

**Formalization Note.** The simulation is the program `stage` with a resampling limit `R`; its
second value is the number of rings observed, `min(Q_T, R + 1)`. Exactness: on the event
`Q_T ≤ R` the limited simulation coincides with the unlimited one, and the probability that it
outputs `τ` on this event tends, as `R → ∞`, to the entry `(σ, τ)` of `e^{−T L_a}`. Time: on every
tape the charged cost is `n + 5 + min(Q_T, R)(⌈log₂(2n)⌉ + 7)` (initialization `n + 5`, each
resampling `⌈log₂(2n)⌉ + 7`). Stated for every matrix `B` with positive entries and rows summing
to `1`, every `J ≥ 0` and every `a > 0`. -/
theorem proposition_15 (n : ℕ) (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) (hB : ∀ u v, 0 < B u v)
    (hrow : ∀ u, ∑ v, B u v = 1) (J : ℝ) (hJ : 0 ≤ J) (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : 0 ≤ T)
    (σ : Asg n) :
    (∀ τ : Asg n, Filter.Tendsto
      (fun R : ℕ => tapeMeasure {ω | (runFree (stage B J a T R σ) ω).1.1 = τ ∧
        (runFree (stage B J a T R σ) ω).1.2 ≤ R})
      Filter.atTop (nhds (ENNReal.ofReal (NormedSpace.exp (-T • glauberLap B J a) σ τ)))) ∧
    ∀ (R : ℕ) (ω : Tape), (runFree (stage B J a T R σ) ω).2 =
      n + 5 + min (runFree (stage B J a T R σ) ω).1.2 R * (Nat.clog 2 (2 * n) + 7) := by sorry

end CubicPermFPRAS
