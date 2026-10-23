-- Prove2me | Theorems.Thm_ForecastComp_IELF_ielf_ic_and_limit_accurate
-- name    : ForecastComp.IELF.ielf_ic_and_limit_accurate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:38.818933+00:00
-- url     : https://prove2.me/theorems/d53018ed-e1df-41ba-baa4-8a6aa0632c13
-- title:
--   Theorems 6 and 7, p. 14 — I-ELF is strictly incentive compatible under belief independence and limit accurate for independent events
-- statement:
--   Let $n\ge2$ and let $R$ be a strictly proper scoring rule with values in $[0,1]$ on reports in $[0,1]$, measurable in the report. Then the Independent-Event Lotteries mechanism $M_{\text{I-ELF}^R}$ — run an ELF lottery (1) on every event, then select the forecaster with the most event wins, breaking ties uniformly at random — has both of the following properties.
--
--   1. **Strict incentive compatibility under belief independence (Theorem 6).** For every number of events $m\ge1$ such that, if $m\ge2$, $R(y,x)<1$ for all $y\in[0,1]$ and $x\in\{0,1\}$: for every forecaster $i$, every belief-independent joint law $D$ of the outcomes and the others' reports with $\mathbb E_D[X]=p_i$, and every $y_i'\in[0,1]^m$ with $y_i'\ne p_i$,
--   $$\Pr_{D}\big(M_{\text{I-ELF}^R}(Y_1,\dots,p_i,\dots,Y_n,X)=i\big)>\Pr_{D}\big(M_{\text{I-ELF}^R}(Y_1,\dots,y_i',\dots,Y_n,X)=i\big).$$
--   2. **Limit accuracy for independent events (Theorem 7).** For every $\underline\Delta>0$ and $\pi\in[0,1)$ there is $\underline m$ such that for all $m\ge\underline m$, all independent outcome laws with marginals $\theta\in[0,1]^m$, all reports $y_1,\dots,y_n\in[0,1]^m$ and every forecaster $i$ whose expected score exceeds every other forecaster's by more than $\underline\Delta$,
--   $$\Pr_{X\sim\theta}\big(M_{\text{I-ELF}^R}(y_1,\dots,y_n,X)=i\big)>\pi.$$
--
--   This is the paper's main result: a forecasting competition with a single prize that is both truthful and, as the number of events grows, selects the most accurate forecaster with probability tending to one.
--
--   **Formalization Note** The two theorems are stated as one conjunction. The condition $R<1$ for $m\ge2$ is part of the mechanism's definition (p. 14, footnote 10). Belief independence is a product of per-event joint laws, and independent outcome laws are given by their marginals.
-- source:
--   Witkowski et al., arXiv:2101.01816v2, p. 14, Theorems 6–7 (proofs pp. 34–36, Appendices L–M)

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

namespace ForecastComp.IELF

/-- Theorems 6 and 7, p. 14: for a strictly proper scoring rule `R` with values in `[0,1]`
(measurable in the report), I-ELF is strictly incentive compatible under belief independence for
every `m ≥ 1` (when `R < 1` on reports in `[0,1]` for `m ≥ 2`, as the mechanism requires), and it
is limit accurate for independent events. -/
theorem ielf_ic_and_limit_accurate {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (hprop : IsStrictlyProper R) (hbdd : IsUnitBounded R)
    (hmeas : ∀ x, Measurable (fun y => R y x)) :
    (∀ m : ℕ, 1 ≤ m → (2 ≤ m → ∀ y ∈ Set.Icc (0:ℝ) 1, ∀ x, R y x < 1) →
        StrictlyICUnderBeliefIndep (ielfSelProb (m := m) (n := n) R)) ∧
    IsLimitAccurateIndep R (fun m θ y i => ielfSelProbIndep (m := m) (n := n) R θ y i) := by sorry

end ForecastComp.IELF
