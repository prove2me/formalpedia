-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_lower_deviation
-- name    : BellWilliams2001.ThresholdPolicy.renewal_lower_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:58:05.804345+00:00
-- url     : https://prove2.me/theorems/f5a8c8d7-012c-4821-be2a-a1edf3c96028
-- title:
--   Appendix A, Eq. (184) — Cramér-type bound on $\mathbf P(N(t)<\chi t)$
-- statement:
--   In the setting of (177)–(179) (as in (181)), let $\varepsilon>0$ with $\chi=\nu-\varepsilon>0$, put $\delta=\varepsilon/(2\nu)$, and let $t\ge0$. Then
--   $$\mathbf P(N(t)<\chi t)\le\exp\Big(-\chi t\,\Lambda^*\Big(\frac1\nu\Big(1+\frac{\varepsilon}{2(\nu-\varepsilon)}\Big)\Big)\Big)+\mathbf P\big(\zeta(1)>\delta t\big).$$
--
--   This is the lower-deviation companion of (181); the second term accounts for the delay $\zeta(1)$, whose law may differ from the others.
--
--   **Formalization Note** The statement is the first member of the chain (184) against its last member. $N(t)\in\mathbb N\cup\{\infty\}$; $\Lambda^*$ takes values in the extended reals.
-- source:
--   Bell and Williams, Dynamic scheduling of a system with two parallel servers in heavy traffic with resource pooling, Ann. Appl. Probab. 11 (2001), p. 645, Appendix A, (184)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

/-- Appendix A, (184) (p. 645), first member against last member: a Cramér-type lower-deviation
bound for a delayed renewal process. Setting of (177)–(179) as in `renewal_upper_deviation`.
For `ε > 0` with `χ = ν − ε > 0`, `δ = ε/(2ν)` and `t ≥ 0`,
`P(N(t) < χt) ≤ exp(−χ t Λ*((1/ν)(1 + ε/(2(ν − ε))))) + P(ζ(1) > δ t)`. -/
theorem renewal_lower_deviation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ζ : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ζ i))
    (hpos : ∀ i ω, 1 ≤ i → 0 < ζ i ω)
    (hindep : iIndepFun (fun i : ℕ => ζ (i + 1)) P)
    (hident : ∀ i, 2 ≤ i → IdentDistrib (ζ i) (ζ 2) P P)
    (hmgf : ∃ δ : ℝ, 0 < δ ∧ ∀ l ∈ Set.Ioo (-δ) δ, ∀ i, 2 ≤ i →
      Integrable (fun ω => Real.exp (l * ζ i ω)) P)
    (ν : ℝ) (hν : ν = 1 / ∫ ω, ζ 2 ω ∂P)
    (ε : ℝ) (hε : 0 < ε) (χ : ℝ) (hχ : χ = ν - ε) (hχpos : 0 < χ)
    (δ : ℝ) (hδ : δ = ε / (2 * ν)) (t : ℝ) (ht : 0 ≤ t) :
    P {ω | (renewalCount (partialSum (fun i => ζ i ω)) t : ℝ≥0∞) < ENNReal.ofReal (χ * t)} ≤
      EReal.exp (-(((χ * t : ℝ) : EReal) *
          legendre (logMGF P (ζ 2)) ((1 / ν) * (1 + ε / (2 * (ν - ε)))))) +
        P {ω | δ * t < ζ 1 ω} := by sorry

end BellWilliams2001.ThresholdPolicy
