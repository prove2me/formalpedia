-- Prove2me | Theorems.Thm_CloudCostOpt_lemma_15_geometric_tail
-- name    : CloudCostOpt.lemma_15_geometric_tail
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:08:40.491792+00:00
-- url     : https://prove2.me/theorems/c050541f-1ad4-4c2f-9562-ee53da8873b2
-- title:
--   Lemma 15 — geometric tail of the late rates $\lambda^x_i(s,l)$ when $\beta_{i,j^{Late,*}_i}\in(0,1)$
-- statement:
--   Let $(i,l)$ with $0\le l\le L_i-1$ be such that $\beta_{i,j^{Late,*}_i}\in(0,1)$, and let
--
--   $$
--   \bar\beta=\max\Big\{\max_{i':\,\beta_{i',j^{Late,*}_{i'}}\in(0,1)}\beta_{i',j^{Late,*}_{i'}},\ \max_{i':\,\beta_{i',j^{Late,*}_{i'}}\in(0,1)}\tilde\beta_{i',j^{Late,*}_{i'}}\Big\}.
--   $$
--
--   Then
--
--   1. (a) for every $s\ge\delta_i$,
--   $$
--   \lambda^x_i(s,l)\le\binom{s}{l}\,\bar\beta^{\,s-\delta_i}\,\lambda_i;
--   $$
--   2. (b) $\displaystyle\sum_{s=\delta_i}^{\infty}\lambda^x_i(s,l)<\infty$.
--
--   Since $\bar\beta<1$, the late rates decay geometrically; this is the case of Lemma 3 in which late orders can fail.
--
--   Differences from the source:
--   - reading: I ≥ 1 order types, Lᵢ ≥ 1 steps and Poisson rates λᵢ > 0, implicit in the model of pp.3–4 → explicit hypotheses 0 < I, 1 ≤ Lᵢ (Standing) and λᵢ > 0; reason: an order has at least one step (the state space is 0 ≤ l ≤ Lᵢ − 1) and a Poisson process has a positive rate
--   - reading: sign of the waiting cost Wᵢ not stated → Wᵢ > 0 (Standing); reason: with Wᵢ = 0 an order can idle forever at no cost, so LB = 0 and (10) fails; the numerical study draws Wᵢ > 0
--   - generalization: j*(i, s, l) and j^{Late,*}_i are "the" argmin → any selection of minimizers (Selection); reason: the paper leaves ties unspecified; its own choice is one selection, so the statement specializes to it
--   - encoding: "for any (i, l)" (λ^x_i(s, l) is defined for 0 ≤ l ≤ Lᵢ − 1) → hypothesis l < Lᵢ; reason: the rates are defined only on that range (and are 0 beyond it)
--   - encoding: Σ_{s=δᵢ}^∞ λ^x_i(s, l) < ∞ → the sum in [0, ∞] is < ⊤; reason: Lean convention for a series of nonnegative terms; same meaning
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, Lemma 15, App. A.5, p.A-6 (PDF p.41)

import Mathlib
import Definitions.Def_CloudCostOpt_rateX
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **Lemma 15** (p.A-6): for any `(i, l)`, `0 ≤ l ≤ Lᵢ − 1`, with `β_{i,j^{Late,*}_i} ∈ (0, 1)`:
(a) for any `s ≥ δᵢ`, `λ^x_i(s, l) ≤ C(s, l) β̄^{s−δᵢ} λᵢ`, where `C(s, l) = s!/(l!(s − l)!)` and
    `β̄ := max{max_{i' : β_{i',j^{Late,*}_{i'}} ∈ (0,1)} β_{i',j^{Late,*}_{i'}},
    max_{i' : β_{i',j^{Late,*}_{i'}} ∈ (0,1)} β̃_{i',j^{Late,*}_{i'}}}`;
(b) `Σ_{s=δᵢ}^∞ λ^x_i(s, l) < ∞`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, Lemma 15, App. A.5, p.A-6 (PDF p.41). -/
theorem lemma_15_geometric_tail (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i) (i : Fin S.I) (l : ℕ) (hl : l < S.L i)
    (hβ : 0 < S.β i (sel.jLate i) ∧ S.β i (sel.jLate i) < 1) :
    let βbar : ℝ :=
      (Finset.univ.filter fun i' => 0 < S.β i' (sel.jLate i') ∧ S.β i' (sel.jLate i') < 1).sup'
        ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hβ⟩⟩
        (fun i' => max (S.β i' (sel.jLate i')) (1 - S.β i' (sel.jLate i')))
    (∀ s, S.δ i ≤ s →
      (rateX S sel lam i s l : ℝ) ≤ (s.choose l : ℝ) * βbar ^ (s - S.δ i) * lam i) ∧
    ∑' k : ℕ, (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) < ⊤ := by sorry

end CloudCostOpt
