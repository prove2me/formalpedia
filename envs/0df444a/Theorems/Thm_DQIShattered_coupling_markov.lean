-- Prove2me | Theorems.Thm_DQIShattered_coupling_markov
-- name    : DQIShattered.coupling_markov
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:43.402195+00:00
-- url     : https://prove2.me/theorems/bff84c8a-aaab-4d36-9d48-c5ff86f9df8d
-- title:
--   Proof of Theorem 2.7, p.16 — $\mathbb P_{B,S}[B_S$ not full rank$]=o_N(1)$ and the Markov step
-- statement:
--   Fix $k\ge3$, $D\ge k$ and an erasure rate $\hat e\in[0,1]$ with $\hat eD<K_*(k)$. Let $B\sim\mathbb G_{\mathrm{ER}}(N,k,D)$, and let $S\subseteq\{1,\dots,M\}$ be independent of $B$, containing each coordinate independently with probability $\hat e$. Then the following hold.
--
--   1. $\mathbb P_{B,S}[B_S\text{ is not full row rank}]\to0$ as $N\to\infty$.
--   2. For every $\delta>0$,
--   $$\mathbb P_B\Big[\mathbb P_S\big(B_S\text{ is not full row rank}\mid B\big)>\delta\Big]\to0\qquad(N\to\infty).$$
--
--   Combined with the USD decoder, the second clause says that with probability $1-o_N(1)$ over $B$ the USD decoder fails with probability at most $\delta$.
--
--   Differences from the source:
--   - encoding: P_{B,S}[B_S is not full row rank] = o_N(1) → the average over uniform hyperedge lists of P_S(B_S not full row rank | B) tends to 0; reason: the joint law of independent B and S; same quantity
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), proof of Theorem 2.7, p.16

import Mathlib
import Definitions.Def_DQIShattered_Ensemble
import Definitions.Def_DQIShattered_Decoding
import Definitions.Def_DQIShattered_Thresholds

namespace DQIShattered

open Filter Topology

/-- Zhou, Shutty, Sellke, Jordan, *Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry*,
arXiv:2609.40345, held version sha256 0c7f6fdf…, proof of Theorem 2.7, p.16 (the coupling and Markov steps).

Fix `k ≥ 3`, `D ≥ k` and an erasure rate `ê ∈ [0, 1]` with `ê D < K_*(k)`. Let `B ∼ 𝔾_ER(N, k, D)` and let `S`
be independent of `B`, each coordinate of `{1, …, M}` erased independently with probability `ê`. Then

1. `P_{B,S}[B_S is not full row rank] → 0` as `N → ∞`;
2. for every `δ > 0`, `P_B[P_S(B_S is not full row rank | B) > δ] → 0` as `N → ∞`.

**Formalization Note** The joint probability is the average over the uniform hyperedge lists of the conditional
failure probability `rankFailProb`. -/
theorem coupling_markov (k : ℕ) (hk : 3 ≤ k) (D : ℝ) (hD : (k : ℝ) ≤ D) (ê : ℝ) (hê0 : 0 ≤ ê)
    (hê1 : ê ≤ 1) (hêD : ê * D < Kstar k) :
    Tendsto (fun N => (∑ E : Fin (Mrows N k D) → KSet N k, rankFailProb (incidence E) ê) /
        (Fintype.card (Fin (Mrows N k D) → KSet N k) : ℝ)) atTop (𝓝 0) ∧
    ∀ δ : ℝ, 0 < δ →
      Tendsto (fun N => erProbB N k D fun B => δ < rankFailProb B ê) atTop (𝓝 0) := by sorry

end DQIShattered
