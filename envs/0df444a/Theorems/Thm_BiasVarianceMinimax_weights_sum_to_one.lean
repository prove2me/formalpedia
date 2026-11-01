-- Prove2me | Theorems.Thm_BiasVarianceMinimax_weights_sum_to_one
-- name    : BiasVarianceMinimax.weights_sum_to_one
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:51.108003+00:00
-- url     : https://prove2.me/theorems/c57ecad0-4944-4a91-a6ee-c975baea6f03
-- title:
--   Appendix C, around (58) — the weights must sum to $1$
-- statement:
--   Let $W$ be a triangular array with $\sum_{j=1}^n w_{j,n}\not\to 1$. Then for every $d>0$ and $\tilde d>0$ there is a model $\hat\theta(\cdot)\in\Theta$ with
--
--   $$R^{gen}(\hat\theta(\cdot),d,\tilde d,W)=\infty.$$
--
--   So any array with finite worst-case risk has sums tending to $1$, and the rest of the analysis can work with such arrays.
--
--   Differences from the source:
--   - generalization: the configuration g(d) of the proof, n₀ = 0 → every d̃ > 0 and every n₀ ∈ ℕ; reason: the argument does not use the relation of d̃ and d
--   - encoding: R_{n_k} → ∞ → the limsup in ℝ≥0∞ equals ⊤; reason: the same statement in extended values
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, Appendix C, (58), p.50

import Mathlib
import Definitions.Def_BiasVarianceMinimax_riskRatio

open Filter Topology

namespace BiasVarianceMinimax

/-- **The weights must sum to `1`.** Lam, Zhang & Zhang, arXiv:1902.04673v1, Appendix C, around (58),
p.50.

An array whose sums do not tend to `1` has infinite risk ratio against some model of `Θ`, for every
`d` and `d̃`.

**Formalization Note.** "`R_{n_k} → ∞`" is the value `⊤` of the `limsup` in `ℝ≥0∞`. The model is
chosen after `W`, `d`, `d̃`; its `θ` is free. -/
theorem weights_sum_to_one (q₁ q₂ : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (n₀ : ℕ) (W : TriangularArray)
    (hW : ¬ Tendsto (fun n : ℕ => ∑ j, W n j) atTop (𝓝 1))
    (d dTilde : ℝ) (hd : 0 < d) (hdTilde : 0 < dTilde) :
    ∃ M : SimulationOutput q₁ q₂, riskRatio M n₀ d dTilde W = ⊤ := by sorry

end BiasVarianceMinimax
