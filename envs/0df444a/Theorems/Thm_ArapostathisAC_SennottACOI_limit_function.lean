-- Prove2me | Theorems.Thm_ArapostathisAC_SennottACOI_limit_function
-- name    : ArapostathisAC.SennottACOI.limit_function
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:44:36.871135+00:00
-- url     : https://prove2.me/theorems/e9dac2f6-c36a-44df-ac2d-36ec3c723b2b
-- title:
--   Proof of Theorem 5.9 — limit policy f, limit function h ≥ −L and constant ρ* along a subsequence β_n → 1
-- statement:
--   In the countable-state controlled Markov process of §5, assume Assumptions 5.14 and 5.16, and Assumption 5.15 with the constant $L\in\mathbb N$, i.e. $h_\beta(i)\ge-L$ for all $i$ and $\beta\in(0,1)$. Let $(\beta_n)$ be a sequence in $(0,1)$ with $\beta_n\to1$, and for each $n$ let $f_{\beta_n}\in\Pi_{SD}$ be $\beta_n$-discount optimal. Then there are a subsequence $(\beta_{n_k})$, a policy $f\in\Pi_{SD}$, a function $h:S\to\mathbb R$ and a constant $\rho^*\ge0$ such that, for every state $i$,
--   $$f_{\beta_{n_k}}(i)\to f(i),\qquad h_{\beta_{n_k}}(i)\to h(i),\qquad (1-\beta_{n_k})J^*_{\beta_{n_k}}(i)\to\rho^*\qquad(k\to\infty),$$
--   and $h(i)\ge-L$.
--
--   This is the first paragraph of the proof of Theorem 5.9: $f$ is a limit point of the discount optimal policies, $h$ comes from Assumption 5.16 and a diagonal argument, and the limit of $(1-\beta_n)J^*_{\beta_n}(i)$ does not depend on $i$.
--
--   **Formalization Note** "$f$ is a limit point of $f_{\beta_n}$" is read as convergence $f_{\beta_{n_k}}(i)\to f(i)$ in $U(i)$ for every $i$ (the product topology on $\Pi_{SD}$, p. 304), along the same subsequence as the other two limits, since the paper passes to a common subsequence. The paper takes $\beta_n\uparrow1$; the statement is made for every sequence in $(0,1)$ tending to $1$, which includes the increasing ones. The constant $L$ of Assumption 5.15 is an explicit argument so that the bound $h\ge-L$ can be stated.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 308, proof of Theorem 5.9, first paragraph

import Mathlib
import Definitions.Def_ArapostathisAC_SennottACOI_CMP
import Definitions.Def_ArapostathisAC_SennottACOI_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.SennottACOI

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- Proof of Theorem 5.9 (p. 308), first paragraph: under Assumptions 5.14–5.16 (with the
constant `L` of Assumption 5.15 named), for every sequence of discount factors `β_n ∈ (0, 1)` with
`β_n → 1` and every choice of `β_n`-discount optimal `f_{β_n} ∈ Π_SD`, there are a subsequence
`φ`, a stationary policy `f`, a function `h : S → ℝ` and a constant `ρ* ≥ 0` such that along the
subsequence `f_{β_n}(i) → f(i)`, `h_{β_n}(i) → h(i)` and `(1 − β_n) J*_{β_n}(i) → ρ*` for every
state `i`, and `h ≥ −L`. -/
theorem limit_function (M : ArapostathisAC.VanishingDiscount.CMP A) (h14 : Assumption5_14 M) (L : ℕ)
    (hL : ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, -(L : ℝ) ≤ ArapostathisAC.VanishingDiscount.hRel M β i) (h16 : Assumption5_16 M)
    (β : ℕ → ℝ) (hβ : ∀ n, β n ∈ Set.Ioo (0 : ℝ) 1) (hβ1 : Tendsto β atTop (𝓝 1))
    (fβ : ℕ → StationaryPolicy M) (hfβ : ∀ n, ArapostathisAC.VanishingDiscount.IsDiscOptimal M (β n) (fβ n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : StationaryPolicy M, ∃ h : ℕ → ℝ, ∃ ρ : ℝ, 0 ≤ ρ ∧
      (∀ i, Tendsto (fun n => (fβ (φ n)).1 i) atTop (𝓝 (f.1 i))) ∧
      (∀ i, Tendsto (fun n => ArapostathisAC.VanishingDiscount.hRel M (β (φ n)) i) atTop (𝓝 (h i))) ∧
      (∀ i, -(L : ℝ) ≤ h i) ∧
      ∀ i, Tendsto (fun n => (1 - β (φ n)) * (ArapostathisAC.VanishingDiscount.discValue M (β (φ n)) i).toReal) atTop
        (𝓝 ρ) := by sorry

end ArapostathisAC.SennottACOI
