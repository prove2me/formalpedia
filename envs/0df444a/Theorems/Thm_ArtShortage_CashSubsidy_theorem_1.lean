-- Prove2me | Theorems.Thm_ArtShortage_CashSubsidy_theorem_1
-- name    : ArtShortage.CashSubsidy.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:47.421313+00:00
-- url     : https://prove2.me/theorems/bf00d177-220c-47b8-abc8-0bff2490acc0
-- title:
--   Theorem 1, p. 16 — the government's optimal cash subsidy: f∗ = min(1, b/c∗), c∗ in four budget regimes
-- statement:
--   Fix $0<g<4$, $1+g<\lambda$ and a Period-1 quantity $q_1\in[0,1]$, and write $B=1+g(1-q_1)$. The government chooses a cash subsidy $(c,f)$ with $cf\le b$. Its choice maximizes Period-2 welfare (eq. (5)) at the trader's best response and, among the maximizers, has the least outlay $cf$.
--
--   There are thresholds $0<b^{CS}_1\le b^{CS}_2\le B$ such that $(c^*,f^*)$ with
--   $$f^*=\min\big(1,\,b/c^*\big)$$
--   is a government choice, where:
--
--   1. if $0\le b\le b^{CS}_1$: $c^*=\big(B-2\sqrt{bB}\big)/2$;
--   2. if $b^{CS}_1<b\le b^{CS}_2$: $c^*=\big(B+\sqrt{B(B+12b)}\big)/6$;
--   3. if $b^{CS}_2<b\le B$: $c^*=\sqrt{bB}$;
--   4. if $b>B$: $c^*=B$.
--
--   Moreover, on the interior of each range ($0<b<b^{CS}_1$, $b^{CS}_1<b<b^{CS}_2$, $b^{CS}_2<b<B$, $b>B$), this $(c^*,f^*)$ is the only government choice.
--
--   The theorem gives the second stage of the backward induction. Theorem 2 and Proposition 3 rest on the trader's Period-2 revenue that it induces.
--
--   **Formalization Note** The thresholds $b^{CS}_1,b^{CS}_2$ are existential. Their closed forms are in the authors' proofs (footnote 11), which are not part of the paper, but the four distinct formulas pin them down. Uniqueness is not claimed at regime boundaries, where two policies may tie, nor at $b=0$, where every policy with $cf=0$ is optimal. The least-outlay tie-break is what yields regime 4. The trader's tie-break toward the larger quantity (footnote 10) is what makes the optimum attained in regime 1.
-- source:
--   Levi, Singhvi & Zheng, Artificial Shortage in Agricultural Supply Chains, SSRN 3332493 (version of 2021-04-14; MSOM forthcoming), p. 16, Theorem 1, footnotes 10–11

import Mathlib
import Definitions.Def_ArtShortage_CashSubsidy_Model

namespace ArtShortage.CashSubsidy

theorem theorem_1 (g lam : ℝ) (hS : Standing g lam) (q1 : ℝ) (hq1 : q1 ∈ Set.Icc (0:ℝ) 1) :
    let cI : ℝ → ℝ := fun b => (1 + g * (1 - q1) - 2 * Real.sqrt (b * (1 + g * (1 - q1)))) / 2
    let cII : ℝ → ℝ := fun b =>
      (1 + g * (1 - q1) + Real.sqrt ((1 + g * (1 - q1)) * (1 + 12 * b + g * (1 - q1)))) / 6
    let cIII : ℝ → ℝ := fun b => Real.sqrt (b * (1 + g * (1 - q1)))
    let cIV : ℝ → ℝ := fun _ => 1 + g * (1 - q1)
    ∃ b1CS b2CS : ℝ, 0 < b1CS ∧ b1CS ≤ b2CS ∧ b2CS ≤ 1 + g * (1 - q1) ∧
      -- (i)
      (∀ b, 0 ≤ b → b ≤ b1CS → IsGovChoice g lam b q1 (cI b) (min 1 (b / cI b))) ∧
      (∀ b, 0 < b → b < b1CS → ∀ c f, IsGovChoice g lam b q1 c f →
        c = cI b ∧ f = min 1 (b / cI b)) ∧
      -- (ii)
      (∀ b, b1CS < b → b ≤ b2CS → IsGovChoice g lam b q1 (cII b) (min 1 (b / cII b))) ∧
      (∀ b, b1CS < b → b < b2CS → ∀ c f, IsGovChoice g lam b q1 c f →
        c = cII b ∧ f = min 1 (b / cII b)) ∧
      -- (iii)
      (∀ b, b2CS < b → b ≤ 1 + g * (1 - q1) →
        IsGovChoice g lam b q1 (cIII b) (min 1 (b / cIII b))) ∧
      (∀ b, b2CS < b → b < 1 + g * (1 - q1) → ∀ c f, IsGovChoice g lam b q1 c f →
        c = cIII b ∧ f = min 1 (b / cIII b)) ∧
      -- (iv)
      (∀ b, 1 + g * (1 - q1) < b → IsGovChoice g lam b q1 (cIV b) (min 1 (b / cIV b))) ∧
      (∀ b, 1 + g * (1 - q1) < b → ∀ c f, IsGovChoice g lam b q1 c f →
        c = cIV b ∧ f = min 1 (b / cIV b)) := by sorry

end ArtShortage.CashSubsidy
