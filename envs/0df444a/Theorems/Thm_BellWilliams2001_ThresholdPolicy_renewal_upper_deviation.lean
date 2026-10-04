-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_upper_deviation
-- name    : BellWilliams2001.ThresholdPolicy.renewal_upper_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:57:57.71322+00:00
-- url     : https://prove2.me/theorems/f9e83695-5135-420a-865f-5f47bc47d05c
-- title:
--   Appendix A, Eq. (181) — Cramér-type bound on $\mathbf P(N(t)>\kappa t)$
-- statement:
--   Let $\zeta(1),\zeta(2),\dots$ be strictly positive independent random variables with $\zeta(2),\zeta(3),\dots$ identically distributed, and suppose $\Lambda(l)=\log\mathbf E e^{l\zeta(i)}<\infty$ for $l$ in a neighbourhood of $0$ and $i\ge2$. Let $m=\mathbf E\zeta(2)$, $\nu=1/m$, $X(n)=\sum_{i=1}^n\zeta(i)$, $N(t)=\sup\{n\ge0:X(n)\le t\}$, and $\Lambda^*$ the Legendre–Fenchel transform of $\Lambda$. For $\varepsilon>0$, $\kappa=\nu+\varepsilon$ and $t>2/\varepsilon$,
--   $$\mathbf P(N(t)>\kappa t)\le\exp\Big(-(\kappa t-1)\Lambda^*\Big(\frac{t}{\kappa t-1}\Big)\Big)\le\exp\Big(-(\kappa t-1)\Lambda^*\Big(\frac1{\nu+\frac12\varepsilon}\Big)\Big).$$
--
--   Together with (184) this controls the deviations of the arrival and service processes from their rates on the time scale of the threshold, and it fixes how large the constant $c$ in $L^r=[c\log r]$ must be.
--
--   **Formalization Note** The paper's fixed index $r$ is suppressed. $N(t)$ takes values in $\mathbb N\cup\{\infty\}$, $\Lambda$ and $\Lambda^*$ in the extended reals, and $\exp(-\infty)=0$.
-- source:
--   Bell and Williams, Dynamic scheduling of a system with two parallel servers in heavy traffic with resource pooling, Ann. Appl. Probab. 11 (2001), pp. 644–645, Appendix A, (177)–(179), (181), (182)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

/-- Appendix A, (181) (p. 644): a Cramér-type upper bound for a delayed renewal process.
`ζ(1), ζ(2), …` (paper's index base; `ζ 0` is unused) are strictly positive independent random
variables, `ζ(2), ζ(3), …` identically distributed, with a finite moment generating function on a
neighbourhood of `0` ((177)); `m = E ζ(2)`, `ν = 1/m`, `X(n) = ∑_{i=1}^n ζ(i)`,
`N(t) = sup{n ≥ 0 : X(n) ≤ t}` ((178)–(179), in `ℕ∞`), `Λ = log E e^{lζ(2)}`, `Λ*` its
Legendre–Fenchel transform (182). For `ε > 0`, `κ = ν + ε` and `t > 2/ε`,
`P(N(t) > κt) ≤ exp(−(κt − 1) Λ*(t/(κt − 1))) ≤ exp(−(κt − 1) Λ*(1/(ν + ε/2)))`.
The paper's fixed index `r` is suppressed. -/
theorem renewal_upper_deviation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ζ : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ζ i))
    (hpos : ∀ i ω, 1 ≤ i → 0 < ζ i ω)
    (hindep : iIndepFun (fun i : ℕ => ζ (i + 1)) P)
    (hident : ∀ i, 2 ≤ i → IdentDistrib (ζ i) (ζ 2) P P)
    (hmgf : ∃ δ : ℝ, 0 < δ ∧ ∀ l ∈ Set.Ioo (-δ) δ, ∀ i, 2 ≤ i →
      Integrable (fun ω => Real.exp (l * ζ i ω)) P)
    (ν : ℝ) (hν : ν = 1 / ∫ ω, ζ 2 ω ∂P)
    (ε : ℝ) (hε : 0 < ε) (κ : ℝ) (hκ : κ = ν + ε) (t : ℝ) (ht : 2 / ε < t) :
    P {ω | ENNReal.ofReal (κ * t) < (renewalCount (partialSum (fun i => ζ i ω)) t : ℝ≥0∞)} ≤
        EReal.exp (-(((κ * t - 1 : ℝ) : EReal) *
          legendre (logMGF P (ζ 2)) (t / (κ * t - 1)))) ∧
      EReal.exp (-(((κ * t - 1 : ℝ) : EReal) *
          legendre (logMGF P (ζ 2)) (t / (κ * t - 1)))) ≤
        EReal.exp (-(((κ * t - 1 : ℝ) : EReal) *
          legendre (logMGF P (ζ 2)) (1 / (ν + ε / 2)))) := by sorry

end BellWilliams2001.ThresholdPolicy
