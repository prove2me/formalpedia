-- Prove2me | Theorems.Thm_ForecastComp_IELF_theorem_2
-- name    : ForecastComp.IELF.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:26.962324+00:00
-- url     : https://prove2.me/theorems/0308613a-ea37-4cc3-9935-1ad563d74820
-- title:
--   Theorem 2, p. 9 — single-event ELF is strictly incentive compatible
-- statement:
--   Consider a single event ($m=1$) and $n\ge2$ forecasters. Let $R$ be a strictly proper scoring rule with values in $[0,1]$, and let $f_i$ be the ELF lottery (1). Fix forecaster $i$ with belief $p\in[0,1]$, and let $D$ be **any** joint law of the outcome $X\in\{0,1\}$ and the reports $Y_j\in[0,1]$ of the other forecasters with $\Pr_D(X=1)=p$; the others' reports may be correlated with $X$ in any way. Then for every report $y'\in[0,1]$ with $y'\ne p$,
--   $$\mathbb E_D\big[f_i(Y_1,\dots,y',\dots,Y_n,X)\big]<\mathbb E_D\big[f_i(Y_1,\dots,p,\dots,Y_n,X)\big].$$
--   Since on one event ELF selects $i$ with probability $f_i$, this is strict incentive compatibility (Definition 2) of ELF for $m=1$.
--
--   It is the single-event building block of Theorem 6: truthful reporting strictly maximizes forecaster $i$'s expected winning probability on each event lottery.
--
--   **Formalization Note** $D$ is a probability measure $\nu$ on $\{0,1\}\times\mathbb R^n$; the $i$-th report coordinate is overwritten by $i$'s report. The scoring rule is assumed measurable in the report so that the expectations exist; reports lie in $[0,1]$ $\nu$-almost surely.
-- source:
--   Witkowski et al., arXiv:2101.01816v2, p. 9, Theorem 2 (proof p. 26, Appendix F); Definition 2, p. 5; eq. (1), p. 8

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

namespace ForecastComp.IELF

open MeasureTheory

/-- Theorem 2, p. 9 (proof p. 26): single-event ELF is strictly incentive compatible
(Definition 2 at `m = 1`). `ν` is an arbitrary joint law of the outcome and all reports; the
`i`-th report coordinate is overwritten by forecaster `i`'s own report. -/
theorem theorem_2 {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (hprop : IsStrictlyProper R) (hbdd : IsUnitBounded R)
    (hmeas : ∀ x, Measurable (fun y => R y x))
    (i : Fin n) (p : ℝ) (ν : Measure (Bool × (Fin n → ℝ))) [IsProbabilityMeasure ν]
    (hmean : ∫ b, (if b.1 then (1:ℝ) else 0) ∂ν = p)
    (hrep : ∀ᵐ b ∂ν, ∀ j, b.2 j ∈ Set.Icc (0:ℝ) 1)
    (y' : ℝ) (hy' : y' ∈ Set.Icc (0:ℝ) 1) (hne : y' ≠ p) :
    ∫ b, elfProb R (Function.update b.2 i y') b.1 i ∂ν <
      ∫ b, elfProb R (Function.update b.2 i p) b.1 i ∂ν := by sorry

end ForecastComp.IELF
