-- Prove2me | Theorems.Thm_DQIShattered_theorem_3_2
-- name    : DQIShattered.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:26.349532+00:00
-- url     : https://prove2.me/theorems/6d0de436-f250-483c-a711-b149c52e9e78
-- title:
--   Theorem 3.2 — $B\sim\mathbb G_{\mathrm{ER}}(N,k,D)$ has full row rank w.h.p. iff $D<K_*(k)$
-- statement:
--   Let $k\ge3$ and $D>0$, and let $B\in\mathbb F_2^{M\times N}$ be the incidence matrix of $\mathbb G_{\mathrm{ER}}(N,k,D)$, with $M=\lfloor ND/k\rfloor$. Then the following hold as $N\to\infty$.
--
--   1. If $D<K_*(k)$, then $\mathbb P[B\text{ has full row rank}]\to1$.
--   2. If $D>K_*(k)$, then $\mathbb P[B\text{ has full row rank}]\to0$.
--
--   This is the sharp full-rank threshold of random sparse $\mathbb F_2$ matrices, adapted from [COKKR24, Theorem 2]. It is what makes the USD erasures decodable below $K_*(k)$.
--
--   Differences from the source:
--   - encoding: 𝔾_ER(N, k, D = kM/N); with high probability → the ensemble with M = ⌊ND/k⌋ rows at fixed D; the probability tends to 1 (resp. 0) as N → ∞; reason: Definition 2.5's row count; kM/N → D
--   - encoding: B has full row rank → the M rows of B are linearly independent over 𝔽₂; reason: same condition
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Theorem 3.2, p.14

import Mathlib
import Definitions.Def_DQIShattered_Ensemble
import Definitions.Def_DQIShattered_Thresholds

namespace DQIShattered

open Filter Topology

/-- Zhou, Shutty, Sellke, Jordan, *Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry*,
arXiv:2609.40345, held version sha256 0c7f6fdf…, Theorem 3.2 (adapted from [COKKR24, Theorem 2]), p.14.

Let `k ≥ 3` and `D > 0`, and let `B ∈ 𝔽₂^{M×N}` be the incidence matrix of `𝔾_ER(N, k, D)`, `M = ⌊ND/k⌋`. If
`D < K_*(k)` then `P[B has full row rank] → 1` as `N → ∞`; if `D > K_*(k)` then `P[B has full row rank] → 0`.

**Formalization Note** "With high probability" is a limit as `N → ∞` at fixed `k, D`; the page's
"`𝔾_ER(N, k, D = kM/N)`" is the ensemble with `M = ⌊ND/k⌋` rows, whose degree `kM/N` tends to `D`. -/
theorem theorem_3_2 (k : ℕ) (hk : 3 ≤ k) (D : ℝ) (hD : 0 < D) :
    (D < Kstar k →
      Tendsto (fun N => erProbB N k D fun B => LinearIndependent (ZMod 2) fun i => B i) atTop (𝓝 1)) ∧
    (Kstar k < D →
      Tendsto (fun N => erProbB N k D fun B => LinearIndependent (ZMod 2) fun i => B i) atTop (𝓝 0)) := by sorry

end DQIShattered
