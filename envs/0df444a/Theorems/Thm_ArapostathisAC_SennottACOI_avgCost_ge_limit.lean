-- Prove2me | Theorems.Thm_ArapostathisAC_SennottACOI_avgCost_ge_limit
-- name    : ArapostathisAC.SennottACOI.avgCost_ge_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:44:53.282547+00:00
-- url     : https://prove2.me/theorems/6e625fc0-e87f-4d66-b1d5-59efbe2c7a16
-- title:
--   Proof of Theorem 5.9 — every policy has average cost at least ρ* = lim (1 − β_n) J*_{β_n}(i)
-- statement:
--   In the countable-state controlled Markov process of §5, assume Assumption 5.14 ($J^*_\beta<\infty$ for all $\beta\in(0,1)$). Let $(\beta_n)$ be a sequence in $(0,1)$ with $\beta_n\to1$, let $i\in S$, and suppose that
--   $$\lim_{n\to\infty}(1-\beta_n)\,J^*_{\beta_n}(i)=\rho^*.$$
--   Then every admissible policy $\pi\in\Pi$ (history dependent, possibly randomized) satisfies
--   $$J(i,\pi)=\limsup_{N\to\infty}\frac1N\,E^\pi_i\sum_{t=0}^{N-1}c(X_t,A_t)\ \ge\ \rho^*.$$
--
--   This is the lower bound of the proof of Theorem 5.9, obtained there from the Tauberian Theorem A.2; combined with $J(i,f)\le\rho^*$ it makes the limit policy $f$ AC-optimal.
--
--   **Formalization Note** The paper's $\rho^*$ is the limit from the first paragraph of the proof; the statement holds for the limit along any sequence $\beta_n\to1$ along which it exists. $J(i,\pi)$ lies in $[0,\infty]$ and the bound reads `ENNReal.ofReal ρ ≤ avgCost M π i`; $\rho^*\ge0$ automatically.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 308, proof of Theorem 5.9 ("By Theorem A.2 in the Appendix, J(i, π) ≥ ρ* for any π ∈ Π")

import Mathlib
import Definitions.Def_ArapostathisAC_SennottACOI_CMP
import Definitions.Def_ArapostathisAC_SennottACOI_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.SennottACOI

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- Proof of Theorem 5.9 (p. 308): "By Theorem A.2 in the Appendix, J(i, π) ≥ ρ* for any π ∈ Π."
Under Assumption 5.14, if `β_n ∈ (0, 1)`, `β_n → 1` and `(1 − β_n) J*_{β_n}(i) → ρ*` for a state
`i`, then every admissible policy `π` (history dependent, randomized) has average cost
`J(i, π) ≥ ρ*`. -/
theorem avgCost_ge_limit (M : ArapostathisAC.VanishingDiscount.CMP A) (h14 : Assumption5_14 M)
    (β : ℕ → ℝ) (hβ : ∀ n, β n ∈ Set.Ioo (0 : ℝ) 1) (hβ1 : Tendsto β atTop (𝓝 1))
    (ρ : ℝ) (i : ℕ)
    (hρ : Tendsto (fun n => (1 - β n) * (ArapostathisAC.VanishingDiscount.discValue M (β n) i).toReal) atTop (𝓝 ρ))
    (π : ArapostathisAC.VanishingDiscount.Policy M) :
    ENNReal.ofReal ρ ≤ ArapostathisAC.VanishingDiscount.avgCost M π i := by sorry

end ArapostathisAC.SennottACOI
