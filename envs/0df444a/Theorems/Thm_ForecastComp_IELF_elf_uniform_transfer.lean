-- Prove2me | Theorems.Thm_ForecastComp_IELF_elf_uniform_transfer
-- name    : ForecastComp.IELF.elf_uniform_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:32.853736+00:00
-- url     : https://prove2.me/theorems/a6befb2a-b166-4825-9ec5-b52964a1e7d1
-- title:
--   Proof of Theorem 6 (Appendix L), p. 34 — an increase of E[F_{i,k}] is a uniform decrease of every E[F_{j,k}]
-- statement:
--   Let $n\ge2$, let $R$ take values in $[0,1]$ on $[0,1]$ and be measurable in the report, and let $\nu$ be a joint law of one event's outcome $X$ and the reports $Y_1,\dots,Y_n\in[0,1]$ (almost surely). For a forecaster $i$ and a report $y\in[0,1]$, write
--   $$q_l(y)=\mathbb E_\nu\big[f_l(Y_1,\dots,y,\dots,Y_n,X)\big]$$
--   for the expected ELF winning probability (1) of forecaster $l$ when $i$ reports $y$. Then for all $y,y'\in[0,1]$:
--
--   1. $\sum_{l=1}^n q_l(y)=1$;
--   2. for every $j\ne i$, $$q_j(y')-q_j(y)=-\frac{q_i(y')-q_i(y)}{n-1}.$$
--
--   So any change in $i$'s expected winning probability on an event is offset by a uniform change in every other forecaster's.
--
--   **Formalization Note** The $i$-th report coordinate of the sample is overwritten by $i$'s report.
-- source:
--   Witkowski et al., arXiv:2101.01816v2, p. 34, proof of Theorem 6 (Appendix L), second paragraph

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

namespace ForecastComp.IELF

open MeasureTheory

/-- Proof of Theorem 6 (Appendix L), p. 34: for one event, with
`q_l(y) = E[f_l]` the expected ELF winning probability of forecaster `l` when `i` reports `y`,
the `q_l(y)` sum to one, and any change in `q_i` is offset by a uniform change of
`−1/(n−1)` times it in every `q_j`, `j ≠ i`. -/
theorem elf_uniform_transfer {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (hbdd : IsUnitBounded R) (hmeas : ∀ x, Measurable (fun y => R y x))
    (ν : Measure (Bool × (Fin n → ℝ))) [IsProbabilityMeasure ν]
    (hrep : ∀ᵐ b ∂ν, ∀ j, b.2 j ∈ Set.Icc (0:ℝ) 1) (i : Fin n)
    (y y' : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) (hy' : y' ∈ Set.Icc (0:ℝ) 1) :
    (∑ l, ∫ b, elfProb R (Function.update b.2 i y) b.1 l ∂ν) = 1 ∧
    ∀ j, j ≠ i →
      (∫ b, elfProb R (Function.update b.2 i y') b.1 j ∂ν) -
          ∫ b, elfProb R (Function.update b.2 i y) b.1 j ∂ν =
        -((∫ b, elfProb R (Function.update b.2 i y') b.1 i ∂ν) -
            ∫ b, elfProb R (Function.update b.2 i y) b.1 i ∂ν) / ((n:ℝ) - 1) := by sorry

end ForecastComp.IELF
