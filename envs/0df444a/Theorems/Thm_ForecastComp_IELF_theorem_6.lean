-- Prove2me | Theorems.Thm_ForecastComp_IELF_theorem_6
-- name    : ForecastComp.IELF.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:32.979807+00:00
-- url     : https://prove2.me/theorems/c833e234-4a01-41a0-912f-0e6dc8d1873c
-- title:
--   Theorem 6, p. 14 — I-ELF is strictly incentive compatible under belief independence
-- statement:
--   Let $n\ge2$ and $m\ge1$, and let $R$ be a strictly proper scoring rule with values in $[0,1]$, measurable in the report, and with values in $[0,1)$ on reports in $[0,1]$ when $m\ge2$ (the requirement of the I-ELF mechanism, p. 14). Then the Independent-Event Lotteries mechanism $M_{\text{I-ELF}^R}$ is strictly incentive compatible under belief independence: for every forecaster $i$, every belief-independent joint law $D$ of the outcomes and the others' reports with $\mathbb E_D[X]=p_i$, and every $y_i'\in[0,1]^m$ with $y_i'\ne p_i$,
--   $$\Pr_{D}\big(M_{\text{I-ELF}^R}(Y_1,\dots,p_i,\dots,Y_n,X)=i\big)>\Pr_{D}\big(M_{\text{I-ELF}^R}(Y_1,\dots,y_i',\dots,Y_n,X)=i\big).$$
--
--   Together with Theorem 7 this is the paper's main result: I-ELF rewards truthful reporting even though only one forecaster is selected.
--
--   **Formalization Note** Belief independence is encoded as a product of per-event joint laws (Definition 8). Measurability of $R$ in the report makes the selection probabilities well-defined expectations.
-- source:
--   Witkowski et al., arXiv:2101.01816v2, p. 14, Theorem 6 (proof p. 34, Appendix L); Definitions 8–9, p. 13; §5.3, pp. 13–14

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

namespace ForecastComp.IELF

/-- Theorem 6, p. 14 (proof p. 34): I-ELF is strictly incentive compatible under belief
independence for `m ≥ 1` events, for `R` a strictly proper scoring rule with values in `[0,1]`
(in `[0,1)` when `m ≥ 2`, as the mechanism requires on p. 14). -/
theorem theorem_6 {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (hprop : IsStrictlyProper R) (hbdd : IsUnitBounded R)
    (hmeas : ∀ x, Measurable (fun y => R y x))
    (m : ℕ) (hm : 1 ≤ m) (hlt : 2 ≤ m → ∀ y ∈ Set.Icc (0:ℝ) 1, ∀ x, R y x < 1) :
    StrictlyICUnderBeliefIndep (ielfSelProb (m := m) (n := n) R) := by sorry

end ForecastComp.IELF
