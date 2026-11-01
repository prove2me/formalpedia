-- Prove2me | Theorems.Thm_CloudCostOpt_lemma_2_poisson_states
-- name    : CloudCostOpt.lemma_2_poisson_states
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:10:35.454679+00:00
-- url     : https://prove2.me/theorems/f1d74019-d43e-4cc3-ae94-5542045dbc54
-- title:
--   Lemma 2 — under $\hat\pi$ the order-state counts, completions and failures are independent Poisson variables
-- statement:
--   Run the policy $\hat\pi$ (every order in order-state $(s,l)$ is sent to $j^*(i,s,l)$). Fix an order type $i$. For every $(s,l)$ with $l\le s$ and $0\le l\le L_i-1$:
--
--   1. (a) $\{x_{i,t}(s,l):t\ge s+2\}$ is a family of i.i.d. Poisson random variables with rate $\lambda^x_i(s,l)$; and for every $t$, the family $\{x_{i,t}(s,l):l\le s\le t-2,\ 0\le l\le L_i-1\}$ is mutually independent;
--   2. (b) $\{y_{i,t}(s,l):t\ge s+2\}$ and $\{\tilde y_{i,t}(s,l):t\ge s+2\}$ are two families of i.i.d. Poisson random variables with rates
--
--   $$
--   \lambda^y_i(s,l)=\beta_{i,j^*(i,s,l)}\,\lambda^x_i(s,l),\qquad\lambda^{\tilde y}_i(s,l)=\tilde\beta_{i,j^*(i,s,l)}\,\lambda^x_i(s,l);
--   $$
--
--   and for every $t$ the family of all $y_{i,t}(s,l)$ and $\tilde y_{i,t}(s,l)$ over $l\le s\le t-2$, $0\le l\le L_i-1$ is mutually independent.
--
--   Here $y_{i,t}(s,l)$ and $\tilde y_{i,t}(s,l)$ are the completions and failures of the cell in period $t$. Lemma 2 is the Poisson-splitting structure behind Corollary 4 and the cost formulas (8) and (11).
--
--   Differences from the source:
--   - reading: I ≥ 1 order types, Lᵢ ≥ 1 steps and Poisson rates λᵢ > 0, implicit in the model of pp.3–4 → explicit hypotheses 0 < I, 1 ≤ Lᵢ (Standing) and λᵢ > 0; reason: an order has at least one step (the state space is 0 ≤ l ≤ Lᵢ − 1) and a Poisson process has a positive rate
--   - reading: sign of the waiting cost Wᵢ not stated → Wᵢ > 0 (Standing); reason: with Wᵢ = 0 an order can idle forever at no cost, so LB = 0 and (10) fails; the numerical study draws Wᵢ > 0
--   - generalization: j*(i, s, l) and j^{Late,*}_i are "the" argmin → any selection of minimizers (Selection); reason: the paper leaves ties unspecified; its own choice is one selection, so the statement specializes to it
--   - reading: rates λ^y_i(s, l) := E[y_{i,s+2}(s, l)], λ^ỹ_i(s, l) := E[ỹ_{i,s+2}(s, l)] → the explicit rates β_{i,j*(i,s,l)} λ^x_i(s, l) and β̃_{i,j*(i,s,l)} λ^x_i(s, l); reason: these are the values computed in the proof (p.A-5); a Poisson law is determined by its mean
--   - encoding: "a set of i.i.d. (mutually independent) random variables" → iIndepFun over the index set, plus the stated Poisson law of each member (HasLaw); reason: Lean convention; same meaning
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, Lemma 2, p.14; rates λ^y = βλ^x, λ^ỹ = β̃λ^x from the proof, pp.A-2–A-5

import Mathlib
import Definitions.Def_CloudCostOpt_piHat
import Definitions.Def_CloudCostOpt_rateX
import Definitions.Def_CloudCostOpt_stateAt
import Definitions.Def_CloudCostOpt_cellSucc
import Definitions.Def_CloudCostOpt_cellFail
import Definitions.Def_CloudCostOpt_sampleMeasure
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **Lemma 2** (p.14): under `π̂`, for every order type `i` and every `(s, l)` with `l ≤ s` and
`0 ≤ l ≤ Lᵢ − 1`:
(a) `{x_{i,t}(s, l) : t ≥ s + 2}` are i.i.d. `Poisson(λ^x_i(s, l))`; and for every `t` the family
    `{x_{i,t}(s, l) : l ≤ s ≤ t − 2, 0 ≤ l ≤ Lᵢ − 1}` is mutually independent;
(b) `{y_{i,t}(s, l) : t ≥ s + 2}` and `{ỹ_{i,t}(s, l) : t ≥ s + 2}` are i.i.d. Poisson with rates
    `λ^y_i(s, l) = β_{i,j*(i,s,l)} λ^x_i(s, l)` and `λ^ỹ_i(s, l) = β̃_{i,j*(i,s,l)} λ^x_i(s, l)`; and for
    every `t` the family of all `y_{i,t}(s, l)` and `ỹ_{i,t}(s, l)` over `l ≤ s ≤ t − 2,
    0 ≤ l ≤ Lᵢ − 1` is mutually independent.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, Lemma 2, p.14; the rates `λ^y = βλ^x`, `λ^ỹ = β̃λ^x` from the proof, App. A.3, pp.A-2–A-5.

Formalization Note: period `t` corresponds to `history … (t − 1)`; `y`, `ỹ` are the completions and
failures of cell `(s, l)` in period `t`. -/
theorem lemma_2_poisson_states (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i) (i : Fin S.I) :
    let P := sampleMeasure S lam
    let π := piHat S sel
    let x : ℕ → ℕ → ℕ → Omega S → ℕ := fun t s l ω => stateAt S π ω (t - 1) i s l
    let y : ℕ → ℕ → ℕ → Omega S → ℕ := fun t s l ω =>
      cellSucc S ω.2 t i s l (π.a (t - 1) (history S π ω (t - 1)) i s l)
    let yf : ℕ → ℕ → ℕ → Omega S → ℕ := fun t s l ω =>
      cellFail S ω.2 t i s l (π.a (t - 1) (history S π ω (t - 1)) i s l)
    -- (a), first sentence
    (∀ s l, l ≤ s → l < S.L i →
      (∀ t, s + 2 ≤ t → HasLaw (x t s l) (poissonMeasure (rateX S sel lam i s l)) P) ∧
      iIndepFun (fun t : {t : ℕ // s + 2 ≤ t} => x t.1 s l) P) ∧
    -- (a), second sentence
    (∀ t, iIndepFun
      (fun c : {c : ℕ × ℕ // c.2 ≤ c.1 ∧ c.1 + 2 ≤ t ∧ c.2 < S.L i} => x t c.1.1 c.1.2) P) ∧
    -- (b), first sentence
    (∀ s l, l ≤ s → l < S.L i →
      (∀ t, s + 2 ≤ t →
        HasLaw (y t s l)
          (poissonMeasure ((S.β i (sel.jStar i s l)).toNNReal * rateX S sel lam i s l)) P ∧
        HasLaw (yf t s l)
          (poissonMeasure ((1 - S.β i (sel.jStar i s l)).toNNReal * rateX S sel lam i s l)) P) ∧
      iIndepFun (fun t : {t : ℕ // s + 2 ≤ t} => y t.1 s l) P ∧
      iIndepFun (fun t : {t : ℕ // s + 2 ≤ t} => yf t.1 s l) P) ∧
    -- (b), second sentence
    (∀ t, iIndepFun
      (fun c : {c : ℕ × ℕ // c.2 ≤ c.1 ∧ c.1 + 2 ≤ t ∧ c.2 < S.L i} ⊕
          {c : ℕ × ℕ // c.2 ≤ c.1 ∧ c.1 + 2 ≤ t ∧ c.2 < S.L i} =>
        Sum.elim (fun c => y t c.1.1 c.1.2) (fun c => yf t c.1.1 c.1.2) c) P) := by sorry

end CloudCostOpt
