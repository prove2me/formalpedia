-- Prove2me | Theorems.Thm_ArapostathisAC_SennottACOI_acoi_limit
-- name    : ArapostathisAC.SennottACOI.acoi_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:44:33.127254+00:00
-- url     : https://prove2.me/theorems/f09f11be-c439-48b6-b44a-5a4581fbba21
-- title:
--   Proof of Theorem 5.9 — the limit (ρ*, h, f) satisfies the average cost optimality inequality
-- statement:
--   In the countable-state controlled Markov process of §5, assume Assumptions 5.14 and 5.16, and Assumption 5.15 with the constant $L\in\mathbb N$. Let $(\beta_n)$ be a sequence in $(0,1)$ with $\beta_n\to1$, let $f_{\beta_n}\in\Pi_{SD}$ be $\beta_n$-discount optimal, and suppose that $f\in\Pi_{SD}$, $h:S\to\mathbb R$ and $\rho^*\in\mathbb R$ satisfy, for every state $i$,
--   $$f_{\beta_n}(i)\to f(i),\qquad h_{\beta_n}(i)\to h(i),\qquad\text{and}\qquad (1-\beta_n)J^*_{\beta_n}(0)\to\rho^*.$$
--   Then for every state $i$ the series $\sum_jP(j\mid i,f(i))\,h(j)$ converges and
--   $$\rho^*+h(i)\ \ge\ c\big(i,f(i)\big)+\sum_jP\big(j\mid i,f(i)\big)\,h(j).$$
--
--   This is the step of the proof of Theorem 5.9 that passes to the limit in (5.15): the pair $(\rho^*,h)$ satisfies the average cost optimality inequality (ACOI) with the action $f(i)$ on the right-hand side.
--
--   **Formalization Note** The limits are those produced by the previous milestone, written as hypotheses. The continuity of $c(i,\cdot)$ and $P(j\mid i,\cdot)$ on $U(i)$ is part of the model. Convergence of the series is part of the conclusion. The sequence is not required to be increasing.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 308, proof of Theorem 5.9, display after "we conclude that"

import Mathlib
import Definitions.Def_ArapostathisAC_SennottACOI_CMP
import Definitions.Def_ArapostathisAC_SennottACOI_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.SennottACOI

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- Proof of Theorem 5.9 (p. 308), the display after "we conclude that": under Assumptions
5.14–5.16 (with the constant `L` of Assumption 5.15 named), let `β_n ∈ (0, 1)` with `β_n → 1`, let
`f_{β_n} ∈ Π_SD` be `β_n`-discount optimal, and suppose `f_{β_n}(i) → f(i)` and
`h_{β_n}(i) → h(i)` for every state `i`, and `(1 − β_n) J*_{β_n}(0) → ρ*`. Then for every state `i`
the series `Σ_j P(j | i, f(i)) h(j)` converges and the average cost optimality inequality
`ρ* + h(i) ≥ c(i, f(i)) + Σ_j P(j | i, f(i)) h(j)` holds. -/
theorem acoi_limit (M : ArapostathisAC.VanishingDiscount.CMP A) (h14 : Assumption5_14 M) (L : ℕ)
    (hL : ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, -(L : ℝ) ≤ ArapostathisAC.VanishingDiscount.hRel M β i) (h16 : Assumption5_16 M)
    (β : ℕ → ℝ) (hβ : ∀ n, β n ∈ Set.Ioo (0 : ℝ) 1) (hβ1 : Tendsto β atTop (𝓝 1))
    (fβ : ℕ → StationaryPolicy M) (hfβ : ∀ n, ArapostathisAC.VanishingDiscount.IsDiscOptimal M (β n) (fβ n))
    (f : StationaryPolicy M) (h : ℕ → ℝ) (ρ : ℝ)
    (hf : ∀ i, Tendsto (fun n => (fβ n).1 i) atTop (𝓝 (f.1 i)))
    (hh : ∀ i, Tendsto (fun n => ArapostathisAC.VanishingDiscount.hRel M (β n) i) atTop (𝓝 (h i)))
    (hρ : Tendsto (fun n => (1 - β n) * (ArapostathisAC.VanishingDiscount.discValue M (β n) 0).toReal) atTop (𝓝 ρ))
    (i : ℕ) :
    Summable (fun j => ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j * h j) ∧
    M.c i (f.1 i) + ∑' j, ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j * h j ≤ ρ + h i := by sorry

end ArapostathisAC.SennottACOI
