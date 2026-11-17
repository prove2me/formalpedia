-- Prove2me | Theorems.Thm_DQIShattered_Supplement_theorem_4_7
-- name    : DQIShattered.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:36:41.69+00:00
-- url     : https://prove2.me/theorems/d9c0c7b5-4378-4cec-954e-e2dc73fd5297
-- title:
--   Theorem 4.7 — Disorder chaos
-- statement:
--   Under every parameter hypothesis of Theorem 4.3, couple $H,H'\sim\mathbb G_{\mathrm{ER}}(N,k,D)$ so that they share their first $M-1$ clauses and their two last clauses are independent. Then
--   $$
--   \liminf_{N\to\infty}\mathbb E\,W_1(\mu_{\beta,H},\mu_{\beta,H'})>0.
--   $$
--   Thus resampling one clause changes the Gibbs law by a nonvanishing expected normalized-Wasserstein amount.
--
--   Differences from the source:
--   - reading: the hypotheses of Theorem 4.3 are incorporated by reference → Lean inlines “sufficiently small” $\varepsilon$, $k\ge k_0(\varepsilon)$, $D\ge k$, and the full interval (4.4); reason: the platform theorem must stand on its own
--   - encoding: the two instances share $M-1$ clauses and independently draw their last clauses → Lean writes the corresponding finite uniform expectation over the shared clause list and both replacement clauses; reason: this is exactly the source coupling, with no independence hidden in a measure-theory convention
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Theorem 4.7, p.19

import Mathlib
import Definitions.Def_DQIShattered_Supplement_Framework

namespace DQIShattered

namespace Supplement

open Filter

/-- **Theorem 4.7 (Disorder Chaos).**
Zhou, Shutty, Sellke, Jordan, arXiv:2609.40345, held version sha256 0c7f6fdf…,
p.19.

Under every hypothesis of Theorem 4.3, couple two Erdős–Rényi instances by sharing their first
`M−1` clauses and drawing both last clauses independently. The liminf of the expected normalized
Wasserstein distance between their Gibbs measures is strictly positive. `oneClauseChange` is
exactly that joint finite average. -/
theorem theorem_4_7 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
        ∀ D : ℝ, (k : ℝ) ≤ D → ∀ β : ℝ, InHardRange k D ε β →
          0 < liminf
            (fun N => oneClauseChange
              (k := k) (D := D) (fun _ B v => gibbs B v β) N) atTop := by sorry

end Supplement

end DQIShattered
