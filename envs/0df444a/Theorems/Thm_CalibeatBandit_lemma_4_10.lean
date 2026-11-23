-- Prove2me | Theorems.Thm_CalibeatBandit_lemma_4_10
-- name    : CalibeatBandit.lemma_4_10
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T18:37:09.38677+00:00
-- url     : https://prove2.me/theorems/53564835-9471-4d1f-80fc-876767e6400b
-- title:
--   Lemma 4.10 — $\mathbb E\max_j|M^{(j)}_T|\le c\sqrt{2T\log(2r)}$ for $r$ martingales with differences bounded by $c$
-- statement:
--   **Lemma 4.10.** Let $(\Omega,P)$ be a probability space with a filtration $(\mathcal F_t)$, let $\iota$ be a finite nonempty index set and $c>0$. For $t<T$ and $j\in\iota$ let $d_t^{(j)}$ be $\mathcal F_{t+1}$-measurable with $|d_t^{(j)}|\le c$ and $\mathbb E[d_t^{(j)}\mid\mathcal F_t]=0$. Then the martingales $M_T^{(j)}=\sum_{t<T}d_t^{(j)}$ satisfy
--
--   $$\mathbb E\Big[\max_{j\in\iota}\big|M_T^{(j)}\big|\Big]\ \le\ c\sqrt{2T\log\big(2|\iota|\big)} .$$
--
--   **Role.** This is the maximal inequality for a finite family of martingales with bounded differences, with no independence between the martingales. In the lower bound it controls, for each action, the difference between the realized swap gains and their conditional means over all swap targets at once.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, Lemma 4.10, p. 20 (proof in Appendix D). Statement taken from jasonhartline's accepted Lean proof of CalibeatBandit.theorem_4_1 (submission 0ae8d87e-4337-4d82-8722-8eeded8a7691).

import Definitions.Def_CalibeatBandit_hard_tree_analysis

set_option autoImplicit false

open CalibeatBandit Filter MeasureTheory Set InformationTheory ProbabilityTheory
open scoped Interval ENNReal BigOperators

theorem CalibeatBandit.lemma_4_10 {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (info : Filtration ℕ mΩ) {T : ℕ} {c : ℝ} (hc : 0 < c)
    (d : ℕ → ι → Ω → ℝ)
    (hm : ∀ t < T, ∀ j, Measurable[info (t + 1)] (d t j))
    (hb : ∀ t < T, ∀ j ω, |d t j ω| ≤ c)
    (hcenter : ∀ t < T, ∀ j, condExp (info t) P (d t j) =ᵐ[P] 0) :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty
      (fun j => |∑ t ∈ Finset.range T, d t j ω|) ∂P) ≤
      c * Real.sqrt (2 * T * Real.log (2 * Fintype.card ι)) := by sorry
